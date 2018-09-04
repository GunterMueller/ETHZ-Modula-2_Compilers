(****************************************
*                                       *
*     MODULA-2 Multi-Pass Compiler      *
*     ****************************      *
*                                       *
*     Implementation for Lilith         *
*                                       *
*                                       *
*     MCP1IO:                           *
*                                       * 
*     input / output handling in Pass 1 *
*                                       * 
*     Version C18 of 11.03.82           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

(* changed to handle tabs 9.9.83 *)

IMPLEMENTATION MODULE MCP1IO;      (* LG *)

  (* $T-,R- *)

  IMPORT
    SYSTEM, NewStreams, WriteStrings, FileLookup, Storage,
    MCBase, MCPublic, MCSymFileDefs, MCP1Reals;

  (* declarations from definition module 

  TYPE String14 = ARRAY [0 .. 13] OF CHAR;

  VAR sy : Symbol;
      val : Constval;
      length : CARDINAL;
      spix : Spellix;

  end of declarations *)

  VAR ch: CHAR;
      pos, line : CARDINAL;

  MODULE OutputSystem;

    FROM NewStreams IMPORT
      STREAM, Connect, Reset, WriteWord, EndWrite, Disconnect;
    FROM Storage IMPORT ALLOCATE, DEALLOCATE;
    FROM MCBase IMPORT Symbol, Spellix;
    FROM MCPublic IMPORT Compilerstatus, compstat, il1File;
    IMPORT sy, val, length, spix, pos, line;

    EXPORT
      PutS, PutSy, PutSyVal, PutIdent, Error,
      InitSave, StopSave, RestartSave, ReleaseSys,
      InitOutput, TermOutput;

    CONST errormax = 300;

    TYPE Syptr = POINTER TO Symb;
         Symb = RECORD next: Syptr; card: CARDINAL END;

    VAR savesys: BOOLEAN;
        first, last: Syptr;
        initline,stopline,restartline: CARDINAL;
        errorcount : CARDINAL;
        Il1 : STREAM;

    PROCEDURE PutSy(s : Symbol);
      VAR c: CARDINAL;
    BEGIN (* put symbol and pos into word *)
      c := ORD(s) * 400B;
      IF pos >= 400B THEN INC(c,377B) ELSE INC(c,pos) END;
      IF savesys THEN
        WITH last^ DO card := c;
          IF next = NIL THEN NEW(next); next^.next := NIL END;
          last := next
        END
      ELSE
        WriteWord(Il1,c);
      END
    END PutSy;

    PROCEDURE PutI(c : CARDINAL);
    BEGIN (* pack c in two bytes *) 
      IF savesys THEN
        WITH last^ DO card := c;
          IF next = NIL THEN NEW(next); next^.next := NIL END;
          last := next
        END;
      ELSE
        WriteWord(Il1,c);
      END
    END PutI;

    PROCEDURE PutS; 
    BEGIN
      PutSy(sy);
      CASE sy OF
        ident : PutI(spix)
       |intcon,cardcon,intcarcon,charcon,realcon : PutI(val.value)
       |stringcon : PutI(val.value); PutI(length)
       |eol : PutI(line)
      ELSE (* nothing *)
      END
    END PutS;

    PROCEDURE PutSyVal(sy: Symbol; val: CARDINAL); 
    BEGIN
      PutSy(sy); PutI(val);
    END PutSyVal;

    PROCEDURE PutIdent(spix: Spellix);
    BEGIN
      PutSy(ident); PutI(spix);
    END PutIdent;

    PROCEDURE Error(n: CARDINAL);
    BEGIN INC(errorcount); INCL(compstat,passerrs);
      IF errorcount <= errormax THEN
        IF errorcount = errormax THEN n := 5 END;
        PutSyVal(errorsy, n)
      ELSIF errorcount >= 10000 THEN HALT; (* LOOP *)
      END;
    END Error;

    PROCEDURE InitSave;
    BEGIN
      savesys := TRUE;
      initline := line;
      restartline := line;
    END InitSave;

    PROCEDURE StopSave;
    BEGIN
      savesys := FALSE;
      IF restartline <> line THEN PutSyVal(eol,line) END;
      stopline := line;
    END StopSave;

    PROCEDURE RestartSave;
    BEGIN
      savesys := TRUE;
      IF stopline <> line THEN PutSyVal(eol,line) END;
      restartline := line;
    END RestartSave;

    PROCEDURE ReleaseSys;
      VAR p : Syptr; 
    BEGIN savesys := FALSE; 
      IF initline <> line THEN PutSyVal(eol, initline) END;
      p := first; 
      WHILE p <> last DO
        WITH p^ DO PutI(card); p := next END;
      END;
      last := first;
      IF stopline <> line THEN PutSyVal(eol, line) END;
    END ReleaseSys;

    PROCEDURE InitOutput;
    BEGIN
      Connect(Il1,il1File,TRUE); Reset(Il1);
      NEW(first); first^.next := NIL;
      initline := 0; stopline := 0; restartline := 0;
      last := first; savesys := FALSE; errorcount := 0;
      EXCL(compstat,passerrs);
    END InitOutput;

    PROCEDURE TermOutput;
    BEGIN
      WHILE first <> NIL DO 
        last := first; first := first^.next;
        DISPOSE(last);
      END;
      PutSy(eop); EndWrite(Il1); Disconnect(Il1,FALSE)
    END TermOutput;

  END OutputSystem;

  MODULE IdentSystem;

    FROM NewStreams IMPORT
      STREAM, Connect, Reset, WriteChar, EndWrite, Disconnect, GetPos;
    FROM Storage IMPORT ALLOCATE, DEALLOCATE;
    FROM MCBase IMPORT Spellix, Symbol;
    FROM MCPublic IMPORT ascFile;
    FROM OutputSystem IMPORT Error;
    IMPORT sy, spix, ch, String14;

    EXPORT
      InIdTab, OutIdTab, TermIdTab, EnterId, GetDmId,
      HashIdent, EnterResWord;

    CONST 
      idmax = 7999; (* provisional for a larger table *)
      idmaxplusone = idmax + 1;
      htabmax = 853; (* MUST BE A PRIME NUMBER *)
      rswlgth = 14; maxspix = 17777B;

    TYPE
      Idindex   = [0..idmax];
      Htindex = [0..htabmax]; 

    VAR
      asc : STREAM;
      idtab : POINTER TO ARRAY Idindex OF CHAR;
      htab : POINTER TO
               ARRAY Htindex OF
                 RECORD
                   identry : [0..idmaxplusone];
                   spix : Spellix;
                 END;
      idbase, idtop, inaux, outaux: CARDINAL;
      dmid: CARDINAL;
      hsix, ix : CARDINAL;

    PROCEDURE GetDmId;
    BEGIN
      INC(dmid); spix := dmid; outaux := 0;
    END GetDmId; 

    PROCEDURE InIdTab; 
    BEGIN
      idtab^[inaux] := ch; hsix := hsix MOD 257*ORD(ch)+1;
      IF inaux < idmax THEN INC(inaux) END
    END InIdTab;

    PROCEDURE OutIdTab;
      (* return character from idtab *)
    BEGIN
      ch := idtab^[outaux];
      INC(outaux);
    END OutIdTab;

    PROCEDURE EnterId;
      VAR h, i, id, b1, b2, dummy: CARDINAL;
    BEGIN
      idtab^[inaux] := ' '; (* separator *)
      IF inaux < idmax THEN INC(inaux) END;
      sy := ident; 
      h := hsix MOD htabmax; hsix := 1;
      IF inaux > idmax THEN GetDmId; Error(7)
      ELSE
        IF h = 0 THEN h := htabmax-1 END;
        i := h;
        LOOP id := htab^[i].identry; 
          IF id > idmax THEN (* a new identifier *) 
            IF inaux+20 < idmax THEN
              GetPos(asc,dummy,spix);
              htab^[i].identry := idtop;
              htab^[i].spix := spix;
              outaux := idtop;
              WHILE idtop < inaux DO
                WriteChar(asc,idtab^[idtop]);
                INC(idtop);
              END;
            ELSE GetDmId; Error(7); inaux := idtop END;
            EXIT
          END;
          b1 := id; b2 := idtop; (* compare identifiers *)
          LOOP
            IF (idtab^[b1]<>idtab^[b2]) OR (b2=inaux) THEN EXIT END;
            INC(b1); INC(b2)
          END;
          IF b2 = inaux THEN inaux := idtop; (* identifier found *) 
            IF id < idbase THEN (* reserved word *)
              sy := VAL(Symbol,ORD(idtab^[b1]));
            ELSE
              outaux := id;
              spix := htab^[i].spix;
            END; 
            EXIT 
          END;
          i := (i+h) MOD htabmax;
          IF i = 0 THEN GetDmId; Error(8); EXIT END
        END
      END
    END EnterId;

    PROCEDURE HashIdent(VAR str: String14);
      VAR l: [0..rswlgth];
    BEGIN l := 0; 
      WHILE (l<rswlgth) AND (str[l]<>0C) DO
        ch := str[l]; InIdTab; INC(l);
      END;
      EnterId;
    END HashIdent;

    PROCEDURE EnterResWord(str: String14; s: Symbol);
    BEGIN
      HashIdent(str); idtab^[idtop] := CHR(ORD(s));
      INC(idtop); inaux := idtop; idbase := idtop;
    END EnterResWord; 

    PROCEDURE TermIdTab;
    BEGIN
      EndWrite(asc); Disconnect(asc,FALSE);
      DISPOSE(idtab);
      DISPOSE(htab);
    END TermIdTab; 

  BEGIN (* initialisation *)
    idbase := 0; idtop := 0; inaux := 0; dmid := maxspix; hsix := 1;
    NEW(idtab);
    NEW(htab);
    FOR ix := 0 TO htabmax DO htab^[ix].identry := idmaxplusone END; 
    Connect(asc,ascFile,FALSE); Reset(asc);
  END IdentSystem;

  MODULE StringSystem;
  
    FROM Storage IMPORT ALLOCATE, DEALLOCATE;
    FROM MCBase IMPORT Stringptr, Constval;
    FROM OutputSystem IMPORT Error;

    EXPORT QUALIFIED PutStrCh, InitString, TermString;

    CONST stringmax = 100;

    TYPE Bufptr = POINTER TO Stringbuffer;
    TYPE Stringbuffer = ARRAY [1 .. stringmax] OF CHAR;

    VAR string : Bufptr;
        strcount : CARDINAL;
        ix : CARDINAL;

    PROCEDURE PutStrCh(ch: CHAR);
      (* put character into stringbuffer *)
    BEGIN
      INC(strcount);
      IF strcount > stringmax THEN
        Error(6);
        strcount := stringmax;
      END;
      string^[strcount] := ch;
    END PutStrCh;

    PROCEDURE InitString;
      (* initalisation of string area *)
    BEGIN
      strcount := 0;
      NEW(string);
    END InitString;

    PROCEDURE TermString(VAR length: CARDINAL; VAR val: Constval);
      VAR buffp : Bufptr;
          ix : CARDINAL;
          sval : Stringptr;
    BEGIN
      length := strcount;
      PutStrCh(0C);
      IF ODD(strcount) THEN PutStrCh(0C) END;
      ALLOCATE(buffp,strcount);
      (* array-structure is overlayed to allocated area *)
      FOR ix := 1 TO strcount DO buffp^[ix] := string^[ix] END;
      DISPOSE(string);
      (* string value entry *)
      NEW(sval);
      WITH sval^ DO
        loadoffset := 177777B; (* initialisation *)
        valentry := CARDINAL(buffp);
        slink := NIL; (* initialisation *)
      END;
      val.svalue := sval;
    END TermString; 

  END StringSystem;

  MODULE SymFileInput;

    FROM NewStreams IMPORT
      STREAM, Connect, Reset, ReadWord, Disconnect;
    FROM WriteStrings IMPORT WriteString, WriteLn;
    FROM FileLookup IMPORT LookupFile;
    FROM Storage IMPORT ALLOCATE;
    FROM MCBase IMPORT Symbol;
    FROM MCPublic IMPORT
      Compilerstatus, compstat, symfileextension;
    FROM MCSymFileDefs IMPORT symFileKey, SymFileSymbols;
    FROM OutputSystem IMPORT PutS, StopSave, RestartSave, Error;
    FROM IdentSystem IMPORT InIdTab, OutIdTab, EnterId;
    FROM StringSystem IMPORT PutStrCh, InitString, TermString;
    IMPORT sy, val, length, spix, ch;

    EXPORT GetSeparateModule;

    CONST maxload = 20; (* maximal number of loaded symbolfiles *)

    TYPE Byte = [0..377B];

    VAR symstream : STREAM;
        buffword : CARDINAL;
        highbyte : BOOLEAN;
        query : BOOLEAN; (* query for symbolfiles *)
        loadsym : ARRAY [1 .. maxload] OF CARDINAL;
                  (* list of symbolfiles already loaded *)
        maxindex, index : CARDINAL;

    PROCEDURE ReadSym(VAR b: Byte);
    BEGIN
      IF highbyte THEN
        b := buffword DIV 400B;
      ELSE
        ReadWord(symstream,buffword);
        b := buffword MOD 400B;
      END;
      highbyte := NOT highbyte;
    END ReadSym;

    PROCEDURE SymGetSy;
      (* get symbol from symstream *)
      CONST rwordnum = 2; (* number of words for a real number *)
      VAR b : Byte;
          ix : CARDINAL;
          rconv : RECORD
                    CASE BOOLEAN OF
                      FALSE : ra : ARRAY [1..rwordnum] OF CARDINAL;
                     |TRUE : rc : REAL;
                    END;
                  END;
    BEGIN
      ReadSym(b);
      (* convert symbols *)
      CASE VAL(SymFileSymbols,b) OF
        endfileSS : sy := eop;
      | unitSS : sy := symbolsy;
      | endunitSS : sy := endblock;
      | importSS : sy := importsy;
      | exportSS : sy := qualifiedsy;
      | constSS : sy := constsy;
      | normalconstSS :
          sy := cardcon;
          ReadSym(b); val.value := b;
          ReadSym(b); val.value := val.value * 400B + b;
      | realconstSS :
          sy := realcon;
          FOR ix := 1 TO rwordnum DO
            ReadSym(b); rconv.ra[ix] := b;
            ReadSym(b); rconv.ra[ix] := rconv.ra[ix] * 400B + b;
          END;
          NEW(val.rvalue);
          val.rvalue^ := rconv.rc;
      | stringconstSS :
          sy := stringcon;
          InitString;
          ReadSym(b);
          (* empty string contains a 0C character *)
          REPEAT PutStrCh(CHR(b)); ReadSym(b) UNTIL b = 0;
          TermString(length,val);
      | typSS : sy := typesy;
      | arraytypSS : sy := arraysy;
      | recordtypSS : sy := recordsy;
      | settypSS : sy := setsy;
      | pointertypSS : sy := pointersy;
      | hiddentypSS : sy := hidden;
      | varSS : sy := varsy;
      | procSS, funcSS : sy := proceduresy;
      | identSS :
          sy := ident;
          ReadSym(b);
          WHILE b <> 0 DO ch := CHR(b); InIdTab; ReadSym(b); END;
          EnterId;
      | periodSS : sy := period;
      | colonSS : sy := colon;
      | rangeSS : sy := range;
      | lparentSS : sy := lparent;
      | rparentSS : sy := rparent;
      | lbracketSS : sy := lbrack;
      | rbracketSS : sy := rbrack;
      | caseSS : sy := casesy;
      | ofSS : sy := ofsy;
      | elseSS : sy := elsesy;
      | endSS : sy := endsy;
      END; (* CASE *)
    END SymGetSy;
 
    PROCEDURE SymFileOK(): BOOLEAN;
      VAR b : Byte;
          key : CARDINAL;
    BEGIN
      ReadSym(b);
      IF b = ORD(normalconstSS) THEN
        ReadSym(b); key := b;
        ReadSym(b); key := key * 400B + b;
        RETURN key = symFileKey;
      ELSE
        RETURN FALSE;
      END;
    END SymFileOK;

    PROCEDURE GetSeparateModule;
      CONST strmax = 24;
      VAR name : ARRAY [0 .. strmax-1] OF CHAR;
          dummyname : ARRAY [0..1] OF CHAR;
          lastinputspix : CARDINAL;
          lastinputch : CHAR;
          lastinputsy : Symbol;
          pos : CARDINAL;
          okfile : BOOLEAN;
          exitcond : BOOLEAN;
          temFile : CARDINAL;
    BEGIN
      lastinputch := ch;
      lastinputspix := spix; 
      lastinputsy := sy; 
      (* test on already loaded symbolfile *)
      index := 1;
      WHILE (index <= maxindex) AND (loadsym[index] <> spix) DO
        INC(index);
      END;
      IF index > maxindex THEN (* new symbolfile *)
        IF maxindex < maxload THEN
          INC(maxindex);
          loadsym[maxindex] := spix;
        END;
        pos := 0;
        OutIdTab;
        WHILE (pos < strmax) AND (ch <> ' ') DO
          name[pos] := ch;
          INC(pos);
          OutIdTab;
        END;
        IF pos < strmax THEN name[pos] := 0C END;
        REPEAT
          exitcond := TRUE;
          LookupFile(name,symfileextension,temFile,
                     query,TRUE,FALSE,
                     dummyname,okfile);
          IF okfile THEN
            Connect(symstream,temFile,TRUE);
            Reset(symstream); 
            highbyte := FALSE;
            IF SymFileOK() THEN
              SymGetSy; SymGetSy; SymGetSy; (* module key *)
              SymGetSy;
              IF (sy = ident) AND (spix = lastinputspix) THEN (* copy file *)
                StopSave;  
                SymGetSy;
                WHILE sy <> eop DO PutS; SymGetSy END;
                RestartSave; 
              ELSE
                WriteString("  ---- incorrect module name");
                WriteLn;
                IF query THEN exitcond := FALSE;
                ELSE INCL(compstat,symerrs);
                END;
              END;
            ELSE
              WriteString("  ---- wrong symbol file");
              WriteLn;
              IF query THEN exitcond := FALSE;
              ELSE INCL(compstat,symerrs);
              END;
            END;
            Disconnect(symstream,TRUE); 
          ELSE
            INCL(compstat,symerrs); (*symbolfiles incomplete*)
          END;
        UNTIL exitcond;
      END;
      ch := lastinputch;
      sy := lastinputsy; 
      spix := lastinputspix; 
    END GetSeparateModule; 

  BEGIN (* SymFileInput *)
    maxindex := 0; (* no symbolfile loaded *)
    query := querys IN compstat;
  END SymFileInput;

  MODULE Scanner;

    FROM NewStreams IMPORT
      STREAM, eolc, Connect, Reset, ReadChar, EOS, Disconnect;
    FROM Storage IMPORT ALLOCATE, DEALLOCATE;
    FROM MCBase IMPORT Symbol;
    FROM MCPublic IMPORT modFile;
    FROM MCP1Reals IMPORT
      InitRealConst, ConvertToFraction, ConvertToExponent,
      TermRealConst;
    FROM OutputSystem IMPORT PutS, PutSyVal, Error;
    FROM IdentSystem IMPORT InIdTab, EnterId;
    FROM StringSystem IMPORT InitString, PutStrCh, TermString;
    IMPORT sy, val, length, spix, ch, line, pos;

    EXPORT GetSy, InitInput, TermInput;

    TYPE Optptr = POINTER TO Opt;
         Opt = RECORD next: Optptr; s: Symbol END;

    CONST illch = 34C;   (* character indicating illegal character in source file *)
          rangech = 35C; (* means same as ".." *)
          eofch = 36C;   (* character indicating end of file *)
          eolch = 37C;   (* character indicating end of line *)
          zero = 60B;    (* ORD('0') *)

    VAR optroot: ARRAY ['A'..'Z'] OF Optptr;
        cch, sch, och: CHAR;
        dval, oval, hval: CARDINAL;
        dok, ook, hok, rok: BOOLEAN;
        input : STREAM;
        mustread : BOOLEAN;

    PROCEDURE NextCh;
    BEGIN
      IF mustread THEN
        ReadChar(input,ch);
        INC(pos);
        IF (ch < 40C) OR (ch > 176C) THEN
          IF ch = eolc THEN ch := eolch;
          ELSIF ch = 11c THEN ch := 40c; (* change tabs to space *) (**)
          ELSIF ch = 0C THEN ch := eofch; mustread := FALSE;
          ELSE ch := illch;
          END;
        END;
      ELSE
        ch := eofch;
      END;
    END NextCh;

    PROCEDURE Comment;
      VAR clevel : CARDINAL; 

      PROCEDURE Options;
        VAR op : Optptr;
      BEGIN
        LOOP WHILE ch = ' ' DO NextCh END;
          IF ch<>'$' THEN EXIT END;
          NextCh; cch := CAP(ch);
          IF (cch<'A') OR ('Z'<cch) THEN EXIT END;
          NextCh;
          IF (ch = '+') OR (ch = '-') OR (ch = '=') THEN
            IF ch = '=' THEN
              IF optroot[cch] <> NIL THEN
                op := optroot[cch];
                optroot[cch] := optroot[cch]^.next;
                DISPOSE(op)
              END;
              IF optroot[cch] = NIL THEN sy := plus;
              ELSE sy := optroot[cch]^.s;
              END;
            ELSE
              IF ch='+' THEN sy := plus ELSE sy := minus END;
              NEW(op);
              WITH op^ DO
                next:=optroot[cch]; optroot[cch]:=op; s:=sy;
              END;
            END;
            PutSyVal(option, ORD(cch));
            PutS; NextCh;
          END;
          sy := eol; (* dummy symbol *)
          WHILE ch = ' ' DO NextCh END;
          IF ch<>',' THEN EXIT ELSE NextCh END
        END; (* LOOP *)
      END Options;

    BEGIN
      clevel := 1;
      Options;
      WHILE (clevel > 0) AND (ch <> eofch) DO
        och := ch; NextCh;
        IF (och='*') AND (ch=')') THEN DEC(clevel); NextCh;
        ELSIF (och='(') AND (ch='*') THEN INC(clevel); NextCh;
        ELSIF och=eolch THEN INC(line); pos := 0; PutS; (*sy=eol*)
        ELSIF och=illch THEN Error(0);
        END;
      END;
      IF clevel > 0 THEN pos := 1; Error(3) END;
    END Comment;

    PROCEDURE GetSy;
      VAR   i: CARDINAL;

      BEGIN
        sy := eol; (* eol is never returned from GetSy *)
        REPEAT och := ch; NextCh;
          CASE och OF
            eofch: sy := eop | 
            eolch: INC(line); pos := 0; PutS |
            illch: Error(0); |
            ' ' : WHILE ch = ' ' DO NextCh END | 
            'A'..'Z','a'..'z': (* identifier or reserved word *)
                  cch := ch; ch := och; InIdTab; ch := cch; cch := CAP(ch);
                  WHILE ('A'<=cch) AND (cch<='Z') OR ('0'<=ch) AND (ch<='9') DO 
                    InIdTab; NextCh; cch := CAP(ch) END;
                  EnterId |
            '0'..'9': (* constant *)
                  InitRealConst;
                  dval := ORD(och) - zero; dok := TRUE;
                  oval := dval; ook := dval < 8;
                  hval := dval; hok := TRUE;
                  ConvertToFraction(och); rok := TRUE;
                  och := ' '; (* for test on octal numbers or characters *)
                  cch := CAP(ch);
                  WHILE ('0'<=ch) AND (ch<='9') OR ('A'<=cch) AND (cch<='F') DO
                    IF ch <= '9' THEN (* digits *)
                      i := ORD(ch) - ORD('0');
                      IF och <> ' ' THEN och := 'H' END;
                    ELSE (* letters 'A' to 'F' *)
                      i := ORD(cch) - ORD('A') + 10;
                      IF (och = ' ') AND ook THEN och := cch ELSE och := 'H' END;
                    END;
                    dok := dok AND ((dval<6553) AND (i<10) OR (dval=6553) AND (i<=5));
                    ook := ook AND (oval < 20000B) AND (i < 8);
                    hok := hok AND (hval < 10000B);
                    rok := rok AND (i < 10);
                    IF dok THEN dval := 10 * dval + i END;
                    IF ook THEN oval := 10B * oval + i END;
                    IF hok THEN hval := 10H * hval + i END;
                    IF rok THEN ConvertToFraction(ch) END;
                    NextCh; cch := CAP(ch);
                  END;
                  sy := intcarcon;
                  IF cch = 'H' THEN (* hexadecimal number *)
                    NextCh;
                    dval := hval;
                    dok := hok;
                  ELSIF och = 'B' THEN (* octal constant *)
                    dval := oval;
                    dok := TRUE;
                  ELSIF och = 'C' THEN (* character constant *)
                    sy := charcon;
                    dval := oval;
                    dok := oval < 400B;
                  ELSIF ch = '.' THEN
                    NextCh;
                    IF ch = '.' THEN ch := rangech;
                    ELSE (* real number *)
                      ConvertToFraction('.');
                      sy := realcon;
                      WHILE ('0' <= ch) AND (ch <='9') DO
                        IF rok THEN ConvertToFraction(ch) END;
                        NextCh;
                      END;
                      IF CAP(ch) = 'E' THEN
                        NextCh;
                        IF (ch = '-') OR (ch = '+') THEN
                          IF ch = '-' THEN ConvertToExponent(ch) END;
                          NextCh;
                        END;
                        IF ('0' <= ch) AND (ch <= '9') THEN
                          REPEAT
                            IF rok THEN ConvertToExponent(ch) END;
                            NextCh;
                          UNTIL (ch < '0') OR ('9' < ch);
                        ELSE rok := FALSE;
                        END;
                      END;
                    END;
                  END;
                  IF sy = realcon THEN
                    IF rok THEN
                      TermRealConst(val,rok);
                      rok := NOT rok; (* inverse error flag *)
                    ELSE val.rvalue := NIL;
                    END;
                    IF NOT rok THEN Error(2) END;
                  ELSIF dok THEN
                    IF (sy=intcarcon) AND (dval>=100000B) THEN
                      sy := cardcon;
                    END;
                    val.value := dval;
                  ELSE  
                    val.value := 0; Error(2);
                  END |
            ':' : IF ch='=' THEN NextCh; sy := becomes
                  ELSE sy := colon END |
            '<' : IF ch = '=' THEN NextCh; sy := leq
                  ELSIF ch='>' THEN NextCh; sy := neq
                  ELSE sy := lss END |
            '>' : IF ch='=' THEN NextCh; sy := geq
                  ELSE sy := grt END |
            '"',"'":
                  i := 0; sy := stringcon;
                  LOOP
                    IF ch = och THEN NextCh; EXIT END;
                    IF (ch < ' ') AND (ch <> illch) THEN Error(4); EXIT END;
                    INC(i);
                    IF i = 1 THEN sch := ch
                    ELSE
                      IF i = 2 THEN InitString; PutStrCh(sch) END;
                      PutStrCh(ch);
                    END;
                    IF ch = illch THEN NextCh; Error(0) ELSE NextCh END;
                  END;
                  IF i = 1 THEN sy:=charcon; val.value := ORD(sch)
                  ELSE
                    IF i = 0 THEN (* empty string *)
                      InitString;
                      PutStrCh(0C);
                    END;
                    TermString(length,val);
                  END |
        rangech : sy := range |
            '.' : IF ch='.' THEN NextCh; sy := range
                  ELSE sy := period END |
            '(' : IF ch='*' THEN NextCh; Comment
                  ELSE sy := lparent END |
            '*' : sy := times |
            '/' : sy := slash |
            '+' : sy := plus |
            '-' : sy := minus |
            '=' : sy := eql | 
            ')' : sy := rparent |
            ',' : sy := comma |
            ';' : sy := semicolon |
            '[' : sy := lbrack |
            ']' : sy := rbrack |
            '^' : sy := arrow |
            '|' : sy := variant |
            '#' : sy := neq | 
            '&' : sy := andsy |
            '{' : sy := lconbr |
            '}' : sy := rconbr
          ELSE Error(0) END;
        UNTIL sy<>eol
      END GetSy;

    PROCEDURE InitInput;
      VAR ch : CHAR;
    BEGIN
      Connect(input,modFile,FALSE); Reset(input);
      line := 1; pos := 0;
      mustread := TRUE;
      FOR ch := 'A' TO 'Z' DO optroot[ch] := NIL END;
      PutSyVal(eol,1);
      NextCh;
    END InitInput;

    PROCEDURE TermInput;
      VAR ch : CHAR;
          op : Optptr;
    BEGIN
      FOR ch := 'A' TO 'Z' DO
        WHILE optroot[ch] <> NIL DO
          op := optroot[ch];
          optroot[ch] := optroot[ch]^.next;
          DISPOSE(op);
        END;
      END;
      Disconnect(input,FALSE);
    END TermInput;

  END Scanner;

  PROCEDURE InitInOut;
  BEGIN
    InitOutput;
    InitInput;
  END InitInOut;

  PROCEDURE TermInOut;
  BEGIN
    TermInput;
    TermOutput;
    TermIdTab;
  END TermInOut;

END MCP1IO.
