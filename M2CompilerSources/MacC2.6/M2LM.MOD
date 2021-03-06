IMPLEMENTATION MODULE M2LM; (* Hermann Seiler, 20.5.85 / 10.6.86 *)
  (*$R- to avoid range errors in the compiler ! *)
  FROM SYSTEM IMPORT WORD, VAL;
  FROM FileSystem IMPORT File, Response, Close, WriteWord;
  FROM FileUtil IMPORT ExtLookup;
  FROM M2DM IMPORT ObjPtr, StrPtr, KeyPtr, ObjClass;
  FROM M2SM IMPORT Mark, IdBuf, Diff, Enter;
  CONST
     CodeLength     = 27000;
     ConstLength    = 5600;
     CodeStartAdr   = 4;  (* pointer to global data space at *)
                          (* PC-relative address 0.          *)
  VAR
     conx           : CARDINAL;
     codeoverflow   : BOOLEAN;
     constoverflow  : BOOLEAN;
     codeB          : ARRAY [ 0 .. CodeLength DIV 2 - 1 ] OF CARDINAL;
     constB         : ARRAY [ 0 .. ConstLength-1] OF CHAR;
  PROCEDURE err(n : CARDINAL);
    (* local synonym for M2SM.Mark. *)
  BEGIN
    Mark(n);
  END err;
  PROCEDURE PutWord(w : WORD);
    (* put a 16-bit word into the code-buffer. *)
  BEGIN
    codeB[pc DIV 2] := VAL(CARDINAL,w);
    IF pc < CodeLength - 100 THEN
      pc := pc + 2
    ELSIF NOT codeoverflow THEN
      codeoverflow := TRUE;
      err(226);
    END;
  END PutWord;
  PROCEDURE PutLong(l : LONGINT);
    (* put a 32-bit longword into the code-buffer. *)
    VAR converter : RECORD
                      CASE :BOOLEAN OF
                        TRUE :  D   : LONGINT
                      | FALSE:  H,L : CARDINAL
                      END
                    END;
  BEGIN converter.D := l;
    PutWord(converter.H);
    PutWord(converter.L);
  END PutLong;
  PROCEDURE AllocString(s : CARDINAL; VAR adr, length : INTEGER);
    (* allocate a string-constant. *)
    VAR L : CARDINAL;
  BEGIN
    adr := (*(maxP + maxM) * 4 +*) conx;
    L   := ORD(IdBuf[s]) - 1; INC(s); length := L;
    IF conx + L + 2 < ConstLength - 10 THEN
      WHILE L > 0 DO
        constB[conx] := IdBuf[s];
        INC(conx); INC(s); DEC(L);
      END;
      constB[conx] := 0C; INC(conx);
      (* assert word-alignment for strings : *)
      IF ODD(conx) THEN constB[conx] := 0C; INC(conx) END;
    ELSIF NOT constoverflow THEN
      constoverflow := TRUE;
      err(225);
    END;
  END AllocString;
  PROCEDURE AllocChar(ch : CHAR; VAR adr : INTEGER);
    (* allocate a character-constant. *)
  BEGIN
    adr := (*(maxP + maxM) * 4 +*) conx;
    IF conx + 2 < ConstLength - 10 THEN
      (* Note : word-alignment is guaranteed by AllocString ! *)
      constB[conx] := ch; INC(conx);
      constB[conx] := 0C; INC(conx);
    ELSIF NOT constoverflow THEN
      constoverflow := TRUE;
      err(225);
    END;
  END AllocChar;
  PROCEDURE AllocBounds(min, max, size : INTEGER; VAR adr : INTEGER);
    (* allocate the bounds of a subrange or index. *)
    VAR L : CARDINAL;
  BEGIN
    adr := 0 (* signal NO bound-pair allocated! *)
  END AllocBounds;
  PROCEDURE fixup(loc : CARDINAL);
    (* enter 16-bit displacement at loc. *)
    VAR x : CARDINAL;
  BEGIN
    x := pc - loc; (* forward distance in bytes *)
    codeB[loc DIV 2] := x;
  END fixup;
  PROCEDURE FixLink(L : CARDINAL);
    VAR L1 : CARDINAL; i: INTEGER;
  BEGIN i := 0;
    WHILE (L > 0) & (L < CodeLength) & (i < 10000) DO
      L1 := codeB[L DIV 2];
      fixup(L);
      L := L1; INC(i);
    END;
  END FixLink;
  PROCEDURE FixupWith(loc : CARDINAL; disp : INTEGER);
    (* enter 16-bit value disp at loc. *)
  BEGIN
    codeB[loc DIV 2] := VAL(CARDINAL,disp);
  END FixupWith;
  PROCEDURE FixLinkWith(L, val : CARDINAL);
    VAR L1 : CARDINAL; i: INTEGER;
  BEGIN i := 0;
    WHILE (L > 0) & (L < CodeLength) & (i < 10000) DO
      L1 := codeB[L DIV 2];
      FixupWith(L, VAL(INTEGER,val) - VAL(INTEGER,L)); (* forward distance *)
      L := L1; INC(i);
    END;
  END FixLinkWith;
  PROCEDURE MergedLinks(L0, L1 : CARDINAL) : CARDINAL;
    (* merge chain of the 2 operands of AND and OR. *)
    VAR L2, L3 : CARDINAL; i: INTEGER;
  BEGIN i := 0;
    IF L0 <> 0 THEN
      L2 := L0;
      LOOP
        L3 := codeB[L2 DIV 2];
        IF (L3 = 0) OR (i >= 10000) THEN EXIT END;
        L2 := L3; INC(i);
      END;
      codeB[L2 DIV 2] := L1;
      RETURN L0;
    ELSE
      RETURN L1
    END;
  END MergedLinks;
  PROCEDURE InitM2LM;
  BEGIN
    pc := CodeStartAdr;
    codeB[0] := 4E71H; codeB[1] := 4E71H; (* NOP's for the Decoder *)
    conx := 0; maxP := 0; maxM := 0;
    codeoverflow := FALSE; constoverflow := FALSE;
  END InitM2LM;
  PROCEDURE OutCodeFile(VAR name : ARRAY OF CHAR; stamp : KeyPtr;
                        datasize : INTEGER; pno, progid : CARDINAL;
                        ModList : ObjPtr);
    CONST HDR = 1; IMP = 2; COD = 3; DAT  = 4;
    VAR   out: File; obj: ObjPtr; i, systemx: CARDINAL; ok: BOOLEAN;
    PROCEDURE W(w: WORD); BEGIN WriteWord(out, w) END W;
    PROCEDURE WriteNameAndKey(id: CARDINAL; stamp: KeyPtr);
      VAR i, j, l, w: CARDINAL; ch: CHAR;
    BEGIN
      l := ORD(IdBuf[id]); j := id;
      FOR i := 1 TO 8 DO
        IF l > 1 THEN INC(j); DEC(l); ch := IdBuf[j] ELSE ch := 0C END;
        w := VAL(CARDINAL,ORD(ch)) * 256;
        IF l > 1 THEN INC(j); DEC(l); ch := IdBuf[j] ELSE ch := 0C END;
        W(w + VAL(CARDINAL,ORD(ch)));
      END;
      IF Diff(id, systemx) = 0 THEN
        W(0); W(0); W(0);
      ELSE
        W(stamp^.k0); W(stamp^.k1); W(stamp^.k2);
      END;
    END WriteNameAndKey;
    PROCEDURE WriteEntries(mod: ObjPtr);
      VAR obj: ObjPtr;
    BEGIN obj := mod^.firstObj;
      WHILE obj # NIL DO
        IF (obj^.class = Proc) & obj^.pd^.exp THEN W(0); W(obj^.pd^.adr)
        ELSIF (obj^.class = Module) THEN WriteEntries(obj)
        END;
        obj := obj^.next
      END
    END WriteEntries;
  BEGIN
    ExtLookup(out, name, TRUE, ok);
    IF NOT ok THEN
      err(222); (* output file not opened *)
      RETURN;
    END;
    systemx := Enter('System');
    (* HeaderBlock *)
    W(HDR); W(34); W(0); WriteNameAndKey(progid, stamp); W(pc);
    W(datasize); W(conx); W(maxP); W(maxM);
    (* ImportBlock *)
    W(IMP); W((maxM-1) * 22); obj := ModList^.next^.next;
    WHILE obj # NIL DO WriteNameAndKey(obj^.name, obj^.key); obj := obj^.next END;
    WriteNameAndKey(systemx, stamp);
    (* CodeBlock *)
    W(COD); W(pc); FOR i := 0 TO pc DIV 2 - 1 DO W(codeB[i]) END;
    (* DataBlock *)
    W(DAT); W((maxP+maxM)*4 + conx); W(0); W(4); WriteEntries(ModList^.next);
    FOR i := 1 TO maxM DO W(0); W(0) END;
    i := 0;
    WHILE i < conx DO
      W(VAL(CARDINAL,ORD(constB[i]))*256 + VAL(CARDINAL,ORD(constB[i+1])));
      i := i + 2;
    END;
    Close(out);
    IF out.res # done THEN
      err(223); (* output incomplete *)
    END;
  END OutCodeFile;
END M2LM. (* Copyright Departement Informatik, ETH Zuerich, Switzerland, 1992 *)
