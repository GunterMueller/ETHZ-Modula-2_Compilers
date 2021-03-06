IMPLEMENTATION MODULE M2SM; (* NW 17.8.83 / 23.3.85; HS 31.5.86 / 30.4.91 *)
  FROM SYSTEM IMPORT LONG, SHORT, VAL;
  FROM FileSystem IMPORT
    File, Response, Lookup, ReadChar, WriteChar, Close;
  FROM FileUtil IMPORT GetPos, SetPos;
  FROM M2DM IMPORT MaxCard, rngchk, ovflchk;
  CONST KW = 43; (* number of keywords *)
        maxDig = 15; (* to avoid floating overflow in scanner *)
        maxExp = 308;(* note the correspondence with the pow-array! *)
        maxBuf = 30; (* maximum length for a number *)
        IdBufLim = IdBufLeng - 100;
        FNM = 300C;
        ERR = 301C;
        MaxOptionLevel = 10;
  VAR ch:     CHAR;      (* current character *)
    id0,id1:  INTEGER;   (* indices of identifier buffer *)
    pow:      ARRAY [0..8] OF LONGREAL;(* must cover exponent range *)
    keyTab:   ARRAY [0..KW-1] OF
                RECORD sym: Symbol; ind: INTEGER END;
    K:        CARDINAL;
    rOptions, vOptions: ARRAY[0..MaxOptionLevel] OF BOOLEAN;
    rIndex,vIndex: INTEGER;
    lastPos:  LONGINT;
    errLog,
    errDat:   File;
  PROCEDURE ErrorBlock(errPos: LONGINT; errCod: CARDINAL);
    VAR i: CARDINAL;
        conv: RECORD
                 CASE :CARDINAL OF
                  0: long: LONGINT
                | 1: sys:  ARRAY [0..3] OF CHAR;
                END;
              END;
  BEGIN
    IF errPos >= 2D THEN errPos := errPos - 2D END;
    WriteChar(errDat, ERR);
    WITH conv DO
      long := errPos; FOR i := 3 TO 0 BY -1 DO WriteChar(errDat, sys[i]) END;
    END;
    WriteChar(errDat,CHR(errCod MOD 256)); WriteChar(errDat,CHR(errCod DIV 256));
  END ErrorBlock;
  PROCEDURE Mark(n: INTEGER);
    VAR k: CARDINAL; buf: CHAR; pos: LONGINT;
      dig: ARRAY [0..3] OF CARDINAL;
  BEGIN scanerr := TRUE; k := 4; GetPos(source, pos);
    IF lastPos + 8D < pos THEN
      ErrorBlock(pos, n);
      IF lastPos + 100D < pos THEN
        lastPos := pos - 100D; SetPos(source, lastPos);
        WriteChar(errLog, 15C); WriteChar(errLog, 15C);
        REPEAT ReadChar(source, buf); INC(lastPos)
        UNTIL (buf = 15C) OR (lastPos = pos)
      ELSE SetPos(source, lastPos)
      END;
      WHILE lastPos < pos DO
        ReadChar(source, buf); WriteChar(errLog, buf); INC(lastPos);
      END;
      WriteChar(errLog, " ");
      REPEAT WriteChar(errLog, "*"); DEC(k) UNTIL k = 0;
      REPEAT dig[k] := n MOD 10; n := n DIV 10; INC(k) UNTIL n = 0;
      REPEAT DEC(k); WriteChar(errLog, CHR(dig[k] + 60B)) UNTIL k = 0;
      WriteChar(errLog, " ")
    END;
  END Mark;
  PROCEDURE GetCh;
  BEGIN ReadChar(source, ch)
  END GetCh;
  (*$R- to speed up and to avoid range errors for invalid i or j *)
  PROCEDURE Diff(i, j: INTEGER): INTEGER;
    VAR k: CARDINAL; d: INTEGER;
  BEGIN
    IF IdBuf[i] # IdBuf[j] THEN
      RETURN VAL(INTEGER,ORD(IdBuf[i])) - VAL(INTEGER,ORD(IdBuf[j]))
    END;
    k := ORD(IdBuf[i])-1; INC(i); INC(j);
    LOOP
      IF k = 0 THEN RETURN 0
      ELSIF IdBuf[i] # IdBuf[j] THEN
        RETURN VAL(INTEGER,ORD(IdBuf[i])) - VAL(INTEGER,ORD(IdBuf[j]))
      ELSE INC(i); INC(j); DEC(k)
      END
    END
  END Diff;
  PROCEDURE KeepId;
  BEGIN id := id1
  END KeepId;
  PROCEDURE String(termCh: CHAR);
  BEGIN id1 := id + 1;
    IF id1 > IdBufLim THEN Mark(91); id1 := 1 END;
    LOOP ReadChar(source, ch);
      IF ch = termCh THEN EXIT END;
      IF ch < " " THEN Mark(45); EXIT END;
      IdBuf[id1] := ch; INC(id1)
    END;
    ReadChar(source, ch);
    IF id1-id <= ORD(MAX(CHAR)) THEN
      IdBuf[id] := CHR(id1-id); (*length*)
    ELSE
      IdBuf[id] := MAX(CHAR);  (*default maximum length*)
      Mark(146);
    END;
    IF IdBuf[id] = 2C THEN
      sym := number; numtyp := 3; intval := ORD(IdBuf[id+1])
    ELSE sym := string;
      IF IdBuf[id] = 1C THEN  (*empty string*)
        IdBuf[id1] := 0C; INC(id1); IdBuf[id] := 2C
      END
    END
  END String;
  PROCEDURE Identifier;
    VAR k, l, m: CARDINAL; cap: BOOLEAN;
  BEGIN id1 := id + 1; cap := TRUE;
    IF id1 > IdBufLim THEN Mark(91); id1 := 1 END;
    REPEAT
      IdBuf[id1] := ch;
      cap := cap AND (ch <= "Z");
      INC(id1); ReadChar(source, ch)
    UNTIL ((CAP(ch) < "A") OR ("Z" < CAP(ch))) & ((ch < "0") OR ("9" < ch));
    IdBuf[id] := CHR(id1-id); (*Length*)
    IF cap THEN
      k := 0; l := KW;
      REPEAT m := (k + l) DIV 2;
        IF Diff(id, keyTab[m].ind) <= 0 THEN l := m ELSE k := m + 1 END
      UNTIL k >= l;
      IF (k < KW) & (Diff(id, keyTab[k].ind) = 0) THEN sym := keyTab[k].sym
      ELSE sym := ident
      END
    ELSE sym := ident
    END
  END Identifier;
  PROCEDURE Number;
    VAR i, j, l, d, e, n: CARDINAL;
    x, f:   LONGREAL;
    d0, d1: LONGINT;
    neg:    BOOLEAN;
    lastCh: CHAR;
    dig:    ARRAY [0..maxBuf] OF CHAR;
    PROCEDURE Ten(e: CARDINAL): LONGREAL;
        VAR k: CARDINAL; u: LONGREAL;
    BEGIN k := 0; u := FLOATD(1);
      WHILE e > 0 DO
        IF ODD(e) THEN u := pow[k] * u END;
        e := e DIV 2; INC(k)
      END;
      RETURN u
    END Ten;
  BEGIN sym := number; i := 0; l := 0;
    REPEAT dig[i] := ch; INC(l);
      IF i < maxBuf THEN INC(i) END;
      ReadChar(source, ch)
    UNTIL (ch < "0") OR ("9" < ch) & (CAP(ch) < "A") OR ("Z" < CAP(ch));
    IF l > maxBuf THEN Mark(46) END; (* too many digits *)
    lastCh := ch; j := 0;
    WHILE (j < i) & (dig[j] = "0") DO INC(j) END;
    IF ch = "." THEN ReadChar(source, ch);
      IF ch = "." THEN
        lastCh := 0C; ch := 177C (*ellipsis*)
      END
    END;
    IF lastCh = "." THEN (*decimal point*)
      x := FLOATD(0); l := 0;
      WHILE j < i DO (*read integer part*)
        IF l < maxDig THEN
          IF dig[j] > "9" THEN Mark(40) END;
          x := x * FLOATD(10) + FLOATD(ORD(dig[j]) - 60B);
          INC(l)
        ELSE Mark(41)
        END;
        INC(j)
      END;
      l := 0; f := FLOATD(0);
      WHILE ("0" <= ch) & (ch <= "9") DO (*read fraction*)
        IF l < maxDig THEN
          f := f * FLOATD(10) + FLOATD(ORD(ch) - 60B);
          INC(l)
        END;
        ReadChar(source, ch)
      END;
      x := f / Ten(l) + x; e := 0; neg := FALSE; numtyp := 4;
      IF (ch = "E") OR (ch = "D") THEN
        IF ch = "D" THEN numtyp := 5 END;
        ReadChar(source, ch);
        IF ch = "-" THEN
          neg := TRUE; ReadChar(source, ch)
        ELSIF ch = "+" THEN ReadChar(source, ch)
        END;
        WHILE ("0" <= ch) & (ch <= "9") DO (*read exponent*)
          d := ORD(ch) - 60B;
          IF (MaxCard - d) DIV 10 >= e THEN (* avoid cardinal ov *)
            e := e*10 + d;
          END;
          ReadChar(source, ch)
        END
      END;
      IF neg THEN
        IF e <= maxExp THEN x := x / Ten(e) ELSE x := FLOATD(0) END
      ELSE
        IF e <= maxExp THEN f := Ten(e);
          IF MAX(LONGREAL) / f >= x THEN x := f*x ELSE Mark(41) END
        ELSE Mark(41)
        END
      END;
      IF numtyp = 5 THEN lrlval := x
      ELSIF x <= LONG(MAX(REAL)) THEN realval := SHORT(x)
      ELSE Mark(41); realval := FLOAT(1)
      END
    ELSE (* integer *)
      lastCh := dig[i-1];
      IF lastCh = "B" THEN DEC(i);
        numtyp := 1; intval := 0;
        WHILE j < i DO
          d := ORD(dig[j]) - 60B;
          IF (d < 10B) & ((MaxCard - d) DIV 10B >= intval) THEN
            intval := 10B * intval + d
          ELSE Mark(29); intval := 0
          END;
          INC(j)
        END
      ELSIF lastCh = "H" THEN DEC(i);
        IF i <= j+4 THEN
          numtyp := 1; intval := 0;
          WHILE j < i DO
            d := ORD(dig[j]) - 60B;
            IF d > 26B THEN Mark(29); d := 0
               ELSIF d > 9 THEN d := d-7
            END;
            intval := 10H * intval + d; INC(j)
          END
        ELSIF i <= j+8 THEN
          numtyp := 2; dblval := 0D;
          REPEAT d := ORD(dig[j]) - 60B;
            IF d > 26B THEN Mark(29); d := 0
               ELSIF d > 9 THEN d := d-7
            END;
            dblval := dblval * 16D + LONG(d); INC(j)
          UNTIL j = i
        ELSE Mark(29); numtyp := 2; dblval := 0D
        END
      ELSIF lastCh = "D" THEN DEC(i);
        numtyp := 2; d1 := 0D;
        WHILE j < i DO
          d := ORD(dig[j]) - 60B;
          IF d < 10 THEN (*no overflow check*)
            d1 := d1 + d1; d0 := d1 + d1; d1 := d0 + d0 + d1 + LONG(d)
          ELSE Mark(29); d1 := 0D
          END;
          INC(j)
        END;
        dblval := d1
      ELSIF lastCh = "C" THEN DEC(i);
        numtyp := 3; intval := 0;
        WHILE j < i DO
          d := ORD(dig[j]) - 60B; intval := 10B * intval + d;
          IF (d >= 10B) OR (intval >= 400B) THEN
            Mark(29); intval := 0
          END;
          INC(j)
        END
      ELSE (* decimal *)
        numtyp := 1; intval := 0;
        WHILE j < i DO
          d := ORD(dig[j]) - 60B;
          IF (d < 10) & ((MaxCard - d) DIV 10 >= intval) THEN
            intval := 10 * intval + d
          ELSE Mark(29); intval := 0
          END;
          INC(j)
        END
      END
    END
  END Number;
(*$R=*)
  PROCEDURE GetSym;
    VAR xch: CHAR;
    PROCEDURE TestOption;
      PROCEDURE MakeOption(VAR stack: ARRAY OF BOOLEAN; VAR index: INTEGER;
                           VAR option: BOOLEAN);
      BEGIN
        ReadChar(source, ch);
        IF    ch = "+" THEN
          stack[index] := option; option := TRUE;
          IF index < MaxOptionLevel THEN INC(index) END;
        ELSIF ch = "-" THEN
          stack[index] := option; option := FALSE;
          IF index < MaxOptionLevel THEN INC(index) END;
        ELSIF ch = "=" THEN
          IF index > 0 THEN DEC(index) END;
          option := stack[index]
        ELSE
          Mark(230)
        END;
      END MakeOption;
    BEGIN
      IF    ch = "R" THEN MakeOption(rOptions, rIndex, rngchk)
      ELSIF ch = "V" THEN MakeOption(vOptions, vIndex, ovflchk)
      ELSE
        Mark(230)  (* invalid option *)
      END
    END TestOption;
    PROCEDURE Comment;
    BEGIN ReadChar(source, ch);
      REPEAT
        IF ch = "$" THEN ReadChar(source, ch); TestOption END;
        WHILE (ch # "*") & (ch > 0C) DO
          IF ch = "(" THEN ReadChar(source, ch);
            IF ch = "*" THEN Comment END
          ELSE ReadChar(source, ch)
          END
        END;
        ReadChar(source, ch)
      UNTIL (ch = ")") OR (ch = 0C);
      IF ch > 0C THEN ReadChar(source, ch) ELSE Mark(42) END
    END Comment;
  BEGIN
    LOOP (*ignore control characters*)
      IF ch <= " " THEN
        IF ch = 0C THEN ch := " "; EXIT ELSE ReadChar(source, ch) END;
      ELSIF ch > 177C THEN ReadChar(source, ch)
      ELSE EXIT
      END
    END;
    CASE ch OF   (* " " <= ch <= 177C *)
        " "  : sym := eof; ch := 0C |
        "!"  : sym := null; ReadChar(source, ch) |
        '"'  : String('"') |
        "#"  : sym := neq; ReadChar(source, ch)  |
        "$"  : sym := null; ReadChar(source, ch) |
        "%"  : sym := null; ReadChar(source, ch) |
        "&"  : sym := and; ReadChar(source, ch)  |
        "'"  : String("'") |
        "("  : ReadChar(source, ch);
               IF ch = "*" THEN Comment; GetSym
                 ELSE sym := lparen
               END |
        ")"  : sym := rparen; ReadChar(source, ch)|
        "*"  : sym := times; ReadChar(source, ch) |
        "+"  : sym := plus; ReadChar(source, ch)  |
        ","  : sym := comma; ReadChar(source, ch) |
        "-"  : sym := minus; ReadChar(source, ch) |
        "."  : ReadChar(source, ch);
               IF ch = "." THEN ReadChar(source, ch); sym := ellipsis
                 ELSE sym := period
               END |
        "/"  : sym := slash; ReadChar(source, ch) |
        "0".."9": Number |
        ":"  : ReadChar(source, ch);
               IF ch = "=" THEN ReadChar(source, ch); sym := becomes
                 ELSE sym := colon
               END |
        ";"  : sym := semicolon; ReadChar(source, ch) |
        "<"  : ReadChar(source, ch);
               IF ch = "=" THEN ReadChar(source, ch); sym := leq
                 ELSIF ch = ">" THEN ReadChar(source, ch); sym := neq
                 ELSE sym := lss
               END |
        "="  : sym := eql; ReadChar(source, ch)   |
        ">"  : ReadChar(source, ch);
               IF ch = "=" THEN ReadChar(source, ch); sym := geq
                 ELSE sym := gtr
               END |
        "?"  : sym := null; ReadChar(source, ch)  |
        "@"  : sym := null; ReadChar(source, ch)  |
        "A".."Z": Identifier       |
        "["  : sym := lbrak; ReadChar(source, ch) |
        "\"  : sym := null; ReadChar(source, ch)  |
        "]"  : sym := rbrak; ReadChar(source, ch) |
        "^"  : sym := arrow; ReadChar(source, ch) |
        "_"  : sym := becomes; ReadChar(source, ch)  |
        "`"  : sym := null; ReadChar(source, ch)  |
        "a".."z": Identifier       |
        "{"  : sym := lbrace; ReadChar(source, ch)|
        "|"  : sym := bar; ReadChar(source, ch)   |
        "}"  : sym := rbrace; ReadChar(source, ch)|
        "~"  : sym := not; ReadChar(source, ch)   |
        177C : sym := ellipsis; ReadChar(source, ch)
    END
  END GetSym;
  PROCEDURE Enter(name: ARRAY OF CHAR): INTEGER;
    VAR j, l: INTEGER;
  BEGIN l := HIGH(name) + 2; id1 := id;
    IF id1+l < IdBufLeng THEN
      IdBuf[id] := CHR(l); INC(id);
      FOR j := 0 TO l-2 DO IdBuf[id] := name[j]; INC(id) END
    END;
    RETURN id1
  END Enter;
  PROCEDURE InitScanner(filename: ARRAY OF CHAR);
    VAR i: CARDINAL;
  BEGIN ch := " "; scanerr := FALSE; lastPos := 0;
    IF id0 = 0 THEN
      id0 := id; Lookup(errLog, "err.LST", TRUE);
      Lookup(errDat, "err.DAT", TRUE);
    ELSE id := id0; WriteChar(errLog, "-"); WriteChar(errLog, 36C)
    END;
    WriteChar(errDat, FNM); i := 0;
    WHILE (i <= VAL(CARDINAL,HIGH(filename))) & (filename[i] # 0C) DO
      WriteChar(errDat, filename[i]); INC(i);
    END;
    WriteChar(errDat, 0C);
    rIndex := 0; vIndex := 0
  END InitScanner;
  PROCEDURE CloseScanner;
  BEGIN Close(errLog); Close(errDat);
  END CloseScanner;
  PROCEDURE EnterKW(sym: Symbol; name: ARRAY OF CHAR);
  VAR l, L: CARDINAL;
  BEGIN
    keyTab[K].sym := sym;
    keyTab[K].ind := id;
    l := 0; L := HIGH(name);
    IdBuf[id] := CHR(L+2); INC(id);
    WHILE l <= L DO
      IdBuf[id] := name[l];
      INC(id); INC(l)
    END;
    INC(K)
  END EnterKW;
BEGIN K := 0; IdBuf[0] := 1C; id := 1; id0 := 0;
  (* assert maxExp < 512 for actual pow! *)
  pow[0] := FLOATD(10)       (* 1.0E1 *);
  pow[1] := pow[0] * pow[0]  (* 1.0E2 *);
  pow[2] := pow[1] * pow[1]  (* 1.0E4 *);
  pow[3] := pow[2] * pow[2]  (* 1.0E8 *);
  pow[4] := pow[3] * pow[3]  (* 1.0E16 *);
  pow[5] := pow[4] * pow[4]  (* 1.0E32 *);
  pow[6] := pow[5] * pow[5]  (* 1.0E64 *);
  pow[7] := pow[6] * pow[6]  (* 1.0E128 *);
  pow[8] := pow[7] * pow[7]  (* 1.0E256 *);
  EnterKW(by,"BY");
  EnterKW(do,"DO");
  EnterKW(if,"IF");
  EnterKW(in,"IN");
  EnterKW(of,"OF");
  EnterKW(or,"OR");
  EnterKW(to,"TO");
  EnterKW(and,"AND");
  EnterKW(div,"DIV");
  EnterKW(end,"END");
  EnterKW(for,"FOR");
  EnterKW(mod,"MOD");
  EnterKW(not,"NOT");
  EnterKW(rem,"REM");
  EnterKW(set,"SET");
  EnterKW(var,"VAR");
  EnterKW(case,"CASE");
  EnterKW(code,"CODE");
  EnterKW(else,"ELSE");
  EnterKW(exit,"EXIT");
  EnterKW(from,"FROM");
  EnterKW(loop,"LOOP");
  EnterKW(then,"THEN");
  EnterKW(type,"TYPE");
  EnterKW(with,"WITH");
  EnterKW(array,"ARRAY");
  EnterKW(begin,"BEGIN");
  EnterKW(const,"CONST");
  EnterKW(elsif,"ELSIF");
  EnterKW(until,"UNTIL");
  EnterKW(while,"WHILE");
  EnterKW(export,"EXPORT");
  EnterKW(import,"IMPORT");
  EnterKW(module,"MODULE");
  EnterKW(record,"RECORD");
  EnterKW(repeat,"REPEAT");
  EnterKW(return,"RETURN");
  EnterKW(forward,"FORWARD");
  EnterKW(pointer,"POINTER");
  EnterKW(procedure,"PROCEDURE");
  EnterKW(qualified,"QUALIFIED");
  EnterKW(definition,"DEFINITION");
  EnterKW(implementation,"IMPLEMENTATION");
END M2SM. (* Copyright Departement Informatik, ETH Zuerich, Switzerland, 1992 *)
