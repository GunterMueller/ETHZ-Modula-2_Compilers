IMPLEMENTATION MODULE M2TA; (* NW 7.4.83; WH 10.1.86; HS 19.12.91 *)
  (* Implementation for the MOTOROLA 68000/68010/68020/68040 processors. *)
  FROM M2DA IMPORT
       WordSize, NilVal, ObjPtr, Object, ObjClass, StrPtr, Structure, StrForm,
       Standard, ParPtr, Parameter, PDesc, PDPtr, KeyPtr, Key,
       mainmod, sysmod, MaxInt,
       undftyp, cardtyp, inttyp, booltyp, chartyp, bitstyp,
       realtyp, lrltyp, lwordtyp, dbltyp, proctyp, notyp, stringtyp,
       addrtyp, bytetyp, wordtyp, ALLOCATE, ResetHeap;
  FROM M2SA IMPORT
       id, Diff, Enter, Mark;
  VAR obj:    ObjPtr;
    universe: ObjPtr;
    BBtyp:    StrPtr;
    expo:     BOOLEAN;
  PROCEDURE FindInScope(id: INTEGER; root: ObjPtr): ObjPtr;
    VAR obj: ObjPtr; d: INTEGER;
  BEGIN obj := root;
    LOOP IF obj = NIL THEN EXIT END;
      d := Diff(id, obj^.name);
      IF d < 0 THEN obj := obj^.left
      ELSIF d > 0 THEN obj := obj^.right
      ELSE EXIT
      END
    END;
    RETURN obj
  END FindInScope;
  PROCEDURE Find(id: INTEGER): ObjPtr;
    VAR obj: ObjPtr;
  BEGIN Scope := topScope;
    LOOP obj := FindInScope(id, Scope^.right);
      IF obj # NIL THEN EXIT END;
      IF Scope^.kind = Module THEN
        obj := FindInScope(id, universe^.right); EXIT
      END;
      Scope := Scope^.left
    END;
    RETURN obj
  END Find;
  PROCEDURE FindImport(id: INTEGER): ObjPtr;
    VAR obj: ObjPtr;
  BEGIN Scope := topScope^.left;
    LOOP obj := FindInScope(id, Scope^.right);
      IF obj # NIL THEN EXIT END;
      IF Scope^.kind = Module THEN
        obj := FindInScope(id, universe^.right); EXIT
      END;
      Scope := Scope^.left
    END;
    RETURN obj
  END FindImport;
  PROCEDURE NewObj(id: INTEGER; cl: ObjClass): ObjPtr;
    VAR ob0, ob1: ObjPtr; d: INTEGER;
  BEGIN ob0 := topScope; ob1 := ob0^.right; d := 1;
    LOOP
      IF ob1 # NIL THEN
        d := Diff(id, ob1^.name);
        IF d < 0 THEN ob0 := ob1; ob1 := ob0^.left
        ELSIF d > 0 THEN ob0 := ob1; ob1 := ob0^.right
        ELSIF ob1^.class = Temp THEN (*export*)
          (*change variant*) ob1^.exported := TRUE;
          topScope^.last^.next := ob1; topScope^.last := ob1; EXIT
        ELSE (*double def*) Mark(100); EXIT
        END
      ELSE (*insert new object*) ALLOCATE(ob1, SIZE(Object));
        IF d < 0 THEN ob0^.left := ob1 ELSE ob0^.right := ob1 END;
        ob1^.left := NIL; ob1^.right := NIL; ob1^.next := NIL;
        IF cl # Temp THEN
          topScope^.last^.next := ob1; topScope^.last := ob1
        END;
        ob1^.exported := FALSE; EXIT
      END
    END;
    WITH ob1^ DO
      name := id; typ := undftyp; class := cl;
      CASE cl OF
      | Header: kind := Proc; last := NIL; heap := NIL; withadr := 0;
      | Const:  WITH conval DO D0 := 0; D1 := 0; D2 := 0; D3 := 0 END;
      | Typ:    mod := mainmod;
      | Var:    varpar := FALSE;
                vmod := 0; vlev := 0; vadr := 0;
      | Field:  offset := 0;
      | Proc:   ALLOCATE(pd, SIZE(PDesc)); firstParam := NIL; firstLocal := NIL;
                pmod := 0;
      | Code:   cd := NIL; firstArg := NIL; std := Halt; cnum := 0;
      | Module: key := NIL; firstObj := NIL; root := NIL; modno := 0;
                typ := notyp;
      | Temp:   baseref := 0;
      END;
    END;
    RETURN ob1
  END NewObj;
  PROCEDURE NewStr(frm: StrForm): StrPtr;
    VAR str: StrPtr;
  BEGIN ALLOCATE(str, SIZE(Structure));
    WITH str^ DO
      strobj := NIL; size := 0; ref := 0; form := frm;
      CASE frm OF
        Undef, Byte, Bool, Char, Int, Enum, Word, LWord, Double,
        Real, LongReal, Opaque, String: |
        Range: RBaseTyp := undftyp; min := 0; max := 0; BndAdr := 0 |
        Pointer: PBaseTyp := undftyp |
        Set:     SBaseTyp := undftyp |
        Array:   ElemTyp := undftyp; IndexTyp := undftyp |
        Record:  firstFld := NIL |
        ProcTyp: firstPar := NIL; resTyp := NIL
      END
    END;
    RETURN str
  END NewStr;
  PROCEDURE NewImp(scope, obj: ObjPtr);
    VAR ob0, ob1, ob1L, ob1R: ObjPtr; d: INTEGER;
  BEGIN ob0 := scope; ob1 := ob0^.right; d := 1;
    LOOP
      IF ob1 # NIL THEN
        d := Diff(obj^.name, ob1^.name);
        IF d < 0 THEN ob0 := ob1; ob1 := ob1^.left
        ELSIF d > 0 THEN ob0 := ob1; ob1 := ob1^.right
        ELSIF ob1^.class = Temp THEN (*exported*)
          ob1L := ob1^.left; ob1R := ob1^.right;
          ob1^ := obj^; ob1^.exported := TRUE;
          ob1^.left := ob1L; ob1^.right := ob1R; EXIT
        ELSE Mark(100); EXIT
        END
      ELSE (*insert copy of imported object*)
        ALLOCATE(ob1, SIZE(Object)); ob1^ := obj^;
        IF d < 0 THEN ob0^.left := ob1 ELSE ob0^.right := ob1 END;
        ob1^.left := NIL; ob1^.right := NIL; ob1^.exported := FALSE;
        IF (obj^.class = Typ) & (obj^.typ^.form = Enum) THEN
          (*import enumeration constants too*)
          ob0 := obj^.typ^.ConstLink;
          WHILE ob0 # NIL DO
            NewImp(scope, ob0); ob0 := ob0^.conval.prev
          END
        END;
        EXIT
      END
    END
  END NewImp;
  PROCEDURE NewPar(ident: INTEGER; isvar: BOOLEAN; last: ParPtr): ParPtr;
    VAR par: ParPtr;
  BEGIN ALLOCATE(par, SIZE(Parameter)); par^.name := ident;
    par^.varpar := isvar; par^.next := last; RETURN par
  END NewPar;
  PROCEDURE NewScope(cl: ObjClass);
    VAR hd: ObjPtr;
  BEGIN ALLOCATE(hd, SIZE(Object));
    WITH hd^ DO
      name := 0; typ := NIL; class := Header;
      left := topScope; right := NIL; last := hd; next := NIL; kind := cl
    END;
    topScope := hd
  END NewScope;
  PROCEDURE CloseScope;
  BEGIN topScope := topScope^.left
  END CloseScope;
  PROCEDURE CheckUDP(obj, node: ObjPtr);
    (*obj is newly defined type; check for undefined forward references
      pointing to this new type by traversing the tree*)
  BEGIN
    IF node # NIL THEN
      IF (node^.class = Typ) & (node^.typ^.form = Pointer) &
         (node^.typ^.PBaseTyp = undftyp) &
         (Diff(node^.typ^.BaseId, obj^.name) = 0) THEN
        node^.typ^.PBaseTyp := obj^.typ
      END;
      CheckUDP(obj, node^.left); CheckUDP(obj, node^.right)
    END
  END CheckUDP;
  PROCEDURE MarkHeap;
  BEGIN ALLOCATE(topScope^.heap, 0); topScope^.name := id
  END MarkHeap;
  PROCEDURE ReleaseHeap;
  BEGIN ResetHeap(topScope^.heap); id := topScope^.name
  END ReleaseHeap;
  PROCEDURE InitTableHandler;
  BEGIN topScope := universe; mainmod^.firstObj := NIL; ReleaseHeap
  END InitTableHandler;
  PROCEDURE EnterTyp(VAR str: StrPtr; name: ARRAY OF CHAR;
                     frm: StrForm; sz: INTEGER);
  BEGIN obj := NewObj(Enter(name), Typ); str := NewStr(frm);
    obj^.typ := str; str^.strobj := obj; str^.size := sz;
    obj^.exported := expo
  END EnterTyp;
  PROCEDURE EnterProc(name: ARRAY OF CHAR; num: Standard; res: StrPtr);
  BEGIN obj := NewObj(Enter(name), Code);
    obj^.typ := res; obj^.std := num; obj^.exported := expo
  END EnterProc;
BEGIN topScope := NIL; Scope := NIL;
  NewScope(Module); universe := topScope;
  undftyp := NewStr(Undef); undftyp^.size := 1;
  notyp := NewStr(Undef); notyp^.size := 0;
  stringtyp := NewStr(String); stringtyp^.size := 0;
  BBtyp := NewStr(Range); (*Bitset Basetyp*)
  ALLOCATE(mainmod, SIZE(Object));
  WITH mainmod^ DO
    class := Module; modno := 0; typ := notyp; next := NIL; exported := FALSE;
    ALLOCATE(key, SIZE(Key))
  END;
  (*initialization of Universe*)
  expo := FALSE;
  EnterTyp(booltyp,  "BOOLEAN",  Bool,     1);
  EnterTyp(chartyp,  "CHAR",     Char,     1);
  EnterTyp(inttyp,   "INTEGER",  Int,      2);
  EnterTyp(cardtyp,  "CARDINAL", Range,    2);
  EnterTyp(bitstyp,  "BITSET",   Set,      WordSize DIV 8);
  EnterTyp(dbltyp,   "LONGINT",  Double,   4);
  EnterTyp(realtyp,  "REAL",     Real,     4);
  EnterTyp(lrltyp,   "LONGREAL", LongReal, 8);
  EnterTyp(proctyp,  "PROC",     ProcTyp,  4);
  (*initialization of module SYSTEM*)
  NewScope(Module);
  expo := TRUE;
  EnterTyp(bytetyp,  "BYTE",      Byte,  1);
  EnterTyp(wordtyp,  "WORD",      Word,  2);
  EnterTyp(lwordtyp, "LONGCARD",  LWord, 4);
  EnterTyp(addrtyp,  "ADDRESS",   LWord, 4);
  EnterProc('ADR',    Adr,    addrtyp);
  EnterProc('TSIZE',  Tsize,  inttyp);
  EnterProc('INLINE', Inline, notyp);
  EnterProc('REG',    Reg,    dbltyp);
  EnterProc('SETREG', Setreg, notyp);
  EnterProc('ASH',    XAsh,   inttyp);
  EnterProc('LSH',    XLsh,   inttyp);
  EnterProc('MSK',    XMsk,   inttyp);
  EnterProc('ROT',    XRot,   inttyp);
  EnterProc('VAL',    Val,    inttyp);
  EnterProc('LONG',   Long,   dbltyp);
  EnterProc('SHORT',  Short,  inttyp);
  EnterProc('Sqrt',   Sqrt,   realtyp);
  EnterProc('Entier', Entier, dbltyp);
  EnterProc('Round',  Round,  dbltyp);
  ALLOCATE(sysmod, SIZE(Object));
  WITH sysmod^ DO
    name := Enter("SYSTEM"); class := Module; modno := 0; exported := FALSE;
    left := NIL; right := NIL; next := NIL;
    firstObj := topScope^.right; root := topScope^.right;
    ALLOCATE(key, SIZE(Key))
  END;
  CloseScope;
  (* initialization of Universe continued *)
  expo := FALSE;
  obj := NewObj(Enter("FALSE"), Const);
  obj^.typ := booltyp; obj^.conval.B := FALSE;
  obj := NewObj(Enter("TRUE"), Const);
  obj^.typ := booltyp; obj^.conval.B := TRUE;
  obj := NewObj(Enter("NIL"), Const);
  obj^.typ := addrtyp; obj^.conval.D := NilVal;
  WITH cardtyp^ DO
    RBaseTyp := inttyp; min := 0; max := MaxInt; size := 2;
  END;
  bitstyp^.SBaseTyp := BBtyp;
  WITH BBtyp^ DO
    RBaseTyp := inttyp; min := 0; max := WordSize - 1; size := 2;
  END;
  proctyp^.firstPar := NIL; proctyp^.resTyp := notyp;
  EnterProc('ABS',    Abs,    inttyp);
  EnterProc('CAP',    Cap,    chartyp);
  EnterProc('CHR',    Chr,    chartyp);
  EnterProc('DEC',    Dec,    notyp);
  EnterProc('EXCL',   Excl,   notyp);
  EnterProc('FLOAT',  Float,  realtyp);
  EnterProc('FLOATD', FloatD, lrltyp);
  EnterProc('HALT',   Halt,   notyp);
  EnterProc('HIGH',   High,   inttyp);
  EnterProc('INC',    Inc,    notyp);
  EnterProc('INCL',   Incl,   notyp);
  EnterProc('LONG',   Long,   dbltyp);
  EnterProc('MAX',    Max,    inttyp);
  EnterProc('MIN',    Min,    inttyp);
  EnterProc('ODD',    Odd,    booltyp);
  EnterProc('ORD',    Ord,    inttyp);
  EnterProc('SHORT',  Short,  inttyp);
  EnterProc('SIZE',   Size,   inttyp);
  EnterProc('TRUNC',  Trunc,  inttyp);
  EnterProc('TRUNCD', TruncD, dbltyp);
  MarkHeap
END M2TA. (* Copyright Departement Informatik, ETH Zuerich, Switzerland, 1992 *)
