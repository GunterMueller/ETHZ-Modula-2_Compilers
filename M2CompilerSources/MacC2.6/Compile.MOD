MODULE Compile; (* NW 6.3.83 / 24.12.85; WH 30.9.87; HS 19.12.91 / 29.5.92 *)
  (* Implementation according to Programming in Modula-2, Third corrected Edition. *)
  FROM SYSTEM IMPORT VAL;
  FROM Terminal IMPORT BusyRead, Read, Write, WriteLn, WriteString;
  FROM FileSystem IMPORT File, Lookup, ReadChar, Response, Close, Delete;
  FROM FileUtil IMPORT Path, termCh, ReadFileName, ExtLookup,
       GetCurrentPath, AddPath;
  IMPORT FPUControl; (* must be first imported compiler module ! *)
  FROM M2Clock IMPORT Time, GetTime;
  FROM M2DM IMPORT
       WordSize, MaxInt, Standard, rngchk, ovflchk,
       inttyp, cardinttyp, cardtyp, realtyp, chartyp, bitstyp, dbltyp, notyp,
       stringtyp, lrltyp, addrtyp, undftyp, mainmod, sysmod,
       ObjPtr, StrPtr, ParPtr, ConstValue, StrForm, ObjClass;
  FROM M2SM IMPORT
       Symbol, sym, id, numtyp, intval, dblval, realval, lrlval, source, IdBuf,
       scanerr, InitScanner, GetSym, Diff, KeepId, Mark, CloseScanner;
  FROM M2TM IMPORT
       topScope, Scope, NewObj, NewStr, NewPar, NewImp,
       NewScope, CloseScope, Find, FindImport, FindInScope, CheckUDP,
       MarkHeap, ReleaseHeap, InitTableHandler;
  FROM M2RM IMPORT
       ModNo, ModList, RefFile,
       InitRef, InRef, OpenRef, RefPoint, OutUnit, CloseRef;
  FROM M2EM IMPORT
       GlbVarStartAdr, LocVarStartAdr, GlbParStartAdr, LocParStartAdr,
       wlev, AllocVar, AllocPar, AllocFld,
       GenItem, GenIndex, GenField, GenDeRef, GenNeg, GenNot, GenAnd,
       GenOr, GenSingSet, GenSet, GenIn, GenOp, GenWith, GenWith2,
       GenStParam, GenStFct, InitM2EM;
  FROM M2CM IMPORT
       LabelRange, ExitTable, curPrio, GenAssign, GenFJ, GenCFJ, GenBJ, GenCBJ,
       PrepCall, GenParam, GenCall, GenEnter, GenResult, GenReturn,
       GenCase1, GenCase2, GenCase3, GenFor1, GenFor2, GenFor3, GenFor4,
       GenLoop1, GenLoop2, GenExit, GenEnterMod, GenExitMod;
  FROM M2HM IMPORT
       DynArrDesSize, ItemMode, Item, curLev,
       WordVal, CheckRegs, SetregMd, SetconMd, LoadD,
       ConvertTyp, CopyDynArray, GenHalt, Processor, ProcessorID, InitM2HM;
  FROM M2LM IMPORT
       pc, AllocString, AllocBounds, fixup, FixLink,
       FixupWith, OutCodeFile, InitM2LM;
  (* sym,id,numtyp,intval,dblval,realval,lrlval are implicit results of GetSym *)
  CONST NL = 63; (* max name length *)
        NofCases     = 128;
        NofExits      = 16;
        LoopLevels     = 4;
        EnumTypSize    = 1;
        SetTypSize     = WordSize DIV 8;
        PointerTypSize = 4;
        ProcTypSize    = 4;
        ESC = 3C;
  VAR ch: CHAR;
      pno: INTEGER;
      mno: INTEGER; (* number of local modules, increasing from 1 *)
      isdef, isimp, ok: BOOLEAN;
      FileName, TempName: ARRAY [0..NL] OF CHAR;
      processor: Processor;
      i: INTEGER;
      TM: Time;
      path: Path;
  PROCEDURE Type(VAR typ: StrPtr); FORWARD;
  PROCEDURE Expression(VAR x: Item); FORWARD;
  PROCEDURE Block(ancestor: ObjPtr; qual: BOOLEAN;
                  VAR adr: INTEGER; VAR L0: CARDINAL); FORWARD;
  PROCEDURE err(n: INTEGER);
  BEGIN Mark(n)
  END err;
  PROCEDURE CheckSym(s: Symbol; n: INTEGER);
  BEGIN
    IF sym = s THEN GetSym ELSE Mark(n) END
  END CheckSym;
  PROCEDURE qualident(VAR obj: ObjPtr);
  BEGIN (*sym = ident*)
    obj := Find(id); GetSym;
    WHILE (sym = period) & (obj # NIL) & (obj^.class = Module) DO
      GetSym;
      IF sym = ident THEN
        obj := FindInScope(id, obj^.root); GetSym;
        IF (obj # NIL) & NOT obj^.exported THEN obj := NIL END
      ELSE err(10)
      END
    END
  END qualident;
  PROCEDURE GenVal(VAR x: Item);
  BEGIN (* convert to a boolean value *)
    IF x.mode = cocMd THEN LoadD(x) END;
  END GenVal;
  PROCEDURE ConstExpression(VAR x: Item);
  BEGIN Expression(x);
    IF x.mode # conMd THEN
      SetconMd(x, 1D, cardtyp); err(44); (* constant expression expected *)
    END
  END ConstExpression;
  PROCEDURE CheckComp(t0, t1: StrPtr);
  BEGIN
    IF (t0 # t1) &
       ((t0 # inttyp) OR (t1 # cardtyp)) &
       ((t0 # cardinttyp) OR (t1 # cardtyp)) THEN err(61) END
  END CheckComp;
  PROCEDURE CaseLabelList(Ltyp: StrPtr;
            VAR n: INTEGER; VAR tab: ARRAY OF LabelRange);
    VAR x,y: Item; i,j: INTEGER; f: StrForm;
  BEGIN f := Ltyp^.form;
    IF f = Range THEN Ltyp := Ltyp^.RBaseTyp
    ELSIF f > Enum THEN err(83)
    END;
    LOOP ConstExpression(x); CheckComp(Ltyp, x.typ);
      IF sym = ellipsis THEN
        GetSym; ConstExpression(y); CheckComp(Ltyp, y.typ);
        IF WordVal(x) > WordVal(y) THEN err(63); y := x END;
      ELSE y := x
      END;
      (*enter label range into ordered table*)  i := n;
      IF i < NofCases THEN
        LOOP
          IF i = 0 THEN EXIT END;
          IF tab[i-1].low <= WordVal(y) THEN
            IF tab[i-1].high >= WordVal(x) THEN err(62) END;
            EXIT
          END;
          tab[i] := tab[i-1]; DEC(i)
        END;
        WITH tab[i] DO
          low := WordVal(x); high := WordVal(y); label := pc
        END;
        INC(n)
      ELSE err(92)
      END;
      IF sym = comma THEN GetSym
      ELSIF (sym = number) OR (sym = ident) THEN err(11)
      ELSE EXIT
      END
    END
  END CaseLabelList;
  PROCEDURE Subrange(VAR typ: StrPtr);
    VAR x, y: Item; f, g: StrForm;
  BEGIN typ := NewStr(Range); ConstExpression(x); f := x.typ^.form;
    IF f <= Enum THEN typ^.min := WordVal(x) ELSE err(82) END;
    CheckSym(ellipsis, 21); ConstExpression(y); g := y.typ^.form;
    CheckComp(x.typ, y.typ);
    WITH typ^ DO max := WordVal(y);
      IF ((f = Card) & (min < 0)) OR ((g = Card) & (max < 0)) THEN
        err(95); min := max
      ELSIF min > max THEN
        err(63); min := max
      END;
      RBaseTyp := x.typ; size := x.typ^.size;
      IF rngchk THEN AllocBounds(min, max, size, BndAdr) END
    END
  END Subrange;
  PROCEDURE SimpleType(VAR typ: StrPtr);
    VAR obj, last: ObjPtr; typ0: StrPtr; n: INTEGER;
  BEGIN typ := undftyp;
    IF sym = ident THEN
      qualident(obj);
      IF (obj # NIL) & (obj^.class = Typ) THEN typ := obj^.typ
        ELSE err(52)
      END;
      IF sym = lbrak THEN
        IF typ^.form = Range THEN typ := typ^.RBaseTyp END;
        GetSym; typ0 := typ; Subrange(typ);
        IF typ^.RBaseTyp # typ0 THEN
          IF (typ0 = inttyp) & (typ^.RBaseTyp = cardtyp) THEN
            typ^.RBaseTyp := inttyp
          ELSE err(61)
          END
        END;
        IF sym = rbrak THEN GetSym ELSE err(16);
          IF sym = rparen THEN GetSym END
        END
      END
    ELSIF sym = lparen THEN
      GetSym; typ := NewStr(Enum); last := NIL; n := 0;
      LOOP
        IF sym = ident THEN
          obj := NewObj(id, Const); KeepId;
          obj^.conval.Ch := VAL(CHAR, n);
          IF n > 255 THEN err(300) END;
          obj^.conval.prev := last; obj^.typ := typ;
          last := obj; INC(n); GetSym
        ELSE err(10)
        END;
        IF sym = comma THEN GetSym
        ELSIF sym = ident THEN err(11)
        ELSE EXIT
        END
      END;
      WITH typ^ DO
        ConstLink := last; NofConst := n; size := EnumTypSize
      END;
      CheckSym(rparen, 15)
    ELSIF sym = lbrak THEN
      GetSym; Subrange(typ);
      IF sym = rbrak THEN GetSym ELSE err(16);
        IF sym = rparen THEN GetSym END
      END
    ELSE err(32)
    END
  END SimpleType;
  PROCEDURE FieldListSequence(VAR maxadr: INTEGER; adr: INTEGER);
    VAR fld1, last, tagfldtyp: ObjPtr; typ: StrPtr;
    PROCEDURE VariantPart;
      (*variables of Fieldlist used: maxadr, adr*)
      VAR lastadr, N: INTEGER;
          tab: ARRAY [0..NofCases-1] OF LabelRange;
    BEGIN maxadr := adr; N := 0;
      LOOP
        IF sym < bar THEN CaseLabelList(typ, N, tab);
          CheckSym(colon, 13); FieldListSequence(lastadr, adr);
          IF lastadr > maxadr THEN maxadr := lastadr END
        END;
        IF sym = bar THEN GetSym ELSE EXIT END
      END;
      IF sym = else THEN
        GetSym; FieldListSequence(lastadr, adr);
        IF lastadr > maxadr THEN maxadr := lastadr END
      END
    END VariantPart;
  BEGIN typ := undftyp;
    IF (sym = ident) OR (sym = case) THEN
      LOOP
        IF sym = ident THEN last := topScope^.last;
          LOOP
            IF sym = ident THEN
              fld1 := NewObj(id, Field); KeepId; GetSym
            ELSE err(10)
            END;
            IF sym = comma THEN GetSym
            ELSIF sym = ident THEN err(11)
            ELSE EXIT
            END
          END;
          CheckSym(colon, 13); Type(typ);
          fld1 := last^.next;
          WHILE fld1 # NIL DO
            fld1^.typ := typ; AllocFld(fld1, adr); fld1 := fld1^.next
          END
        ELSIF sym = case THEN
          GetSym; fld1 := NIL; tagfldtyp := NIL;
          IF sym = ident THEN
            fld1 := NewObj(id, Field); KeepId; GetSym
          END;
          CheckSym(colon, 13);
          IF sym = ident THEN qualident(tagfldtyp)
            ELSE err(10)
          END;
          IF (tagfldtyp # NIL) & (tagfldtyp^.class = Typ) THEN
            typ := tagfldtyp^.typ
          ELSE err(52)
          END;
          IF fld1 # NIL THEN fld1^.typ := typ; AllocFld(fld1, adr) END;
          CheckSym(of, 23); VariantPart; adr := maxadr;
          CheckSym(end, 20)
        END;
        IF sym = semicolon THEN GetSym
        ELSIF sym = ident THEN err(12)
        ELSE EXIT
        END
      END
    END;
    maxadr := adr
  END FieldListSequence;
  PROCEDURE FormalType(VAR typ: StrPtr);
    VAR objtyp: ObjPtr;
  BEGIN typ := undftyp;
    IF sym = array THEN
      GetSym; typ := NewStr(Array);
      WITH typ^ DO
        strobj := NIL; size := DynArrDesSize; dyn := TRUE
      END;
      CheckSym(of, 23);
      IF sym = ident THEN
        qualident(objtyp);
        IF (objtyp # NIL) & (objtyp^.class = Typ) THEN
          typ^.ElemTyp := objtyp^.typ
        ELSE err(52)
        END
      ELSE err(10)
      END
    ELSIF sym = ident THEN
      qualident(objtyp);
      IF (objtyp # NIL) & (objtyp^.class = Typ) THEN
        typ := objtyp^.typ
      ELSE typ := undftyp; err(52)
      END
    ELSE err(10)
    END
  END FormalType;
  PROCEDURE FormalTypeList(proctyp: StrPtr);
    VAR obj: ObjPtr; par, par0, par1: ParPtr; isvar: BOOLEAN;
  BEGIN par := NIL;
    IF (sym = ident) OR (sym = var) OR (sym = array) THEN
      LOOP
        IF sym = var THEN GetSym; isvar := TRUE ELSE isvar := FALSE END;
        par := NewPar(0, isvar, par); FormalType(par^.typ);
        IF sym = comma THEN GetSym
        ELSIF sym = ident THEN err(11)
        ELSE EXIT
        END
      END
    END;
    CheckSym(rparen, 15); (* reverse list *)
    par1 := NIL; (*reverse list*)
    WHILE par # NIL DO
      par0 := par; par := par0^.next; par0^.next := par1; par1 := par0
    END;
    proctyp^.firstPar := par1;
    IF sym = colon THEN
      GetSym; proctyp^.resTyp := undftyp;
      IF sym = ident THEN qualident(obj);
        IF (obj # NIL) & (obj^.class = Typ) THEN proctyp^.resTyp := obj^.typ
          ELSE err(52)
        END
      ELSE err(10)
      END
    ELSE proctyp^.resTyp := notyp
    END
  END FormalTypeList;
  PROCEDURE ArrayType(VAR typ: StrPtr);
    VAR a,b: INTEGER;
  BEGIN typ := NewStr(Array); typ^.dyn := FALSE; a := 0;
    SimpleType(typ^.IndexTyp);
    WITH typ^.IndexTyp^ DO
      IF form # Range THEN
        err(94); form := Range; RBaseTyp := inttyp; min := 0; max := 0
      END;
      a := min; b := max
    END;
    IF sym = of THEN
      GetSym; Type(typ^.ElemTyp)
    ELSIF sym = comma THEN
      GetSym; ArrayType(typ^.ElemTyp)
    ELSE err(23)
    END;
    IF b >= 0 THEN
      IF b - MaxInt >= a THEN err(210); a := b END
    ELSIF a < 0 THEN
      IF b >= a + MaxInt THEN err(210); a := b END
    END;
    a := b-a+1; b := typ^.ElemTyp^.size;
    IF (b = 0) OR (MaxInt DIV b >= a) THEN a := a*b ELSE err(210); a := 4 END;
    typ^.size := VAL(INTEGER, VAL(CARDINAL, -a) MOD 2) + a (*%*)
  END ArrayType;
  PROCEDURE Type(VAR typ: StrPtr);
    VAR obj: ObjPtr; btyp: StrPtr;
  BEGIN
    IF sym < lparen THEN err(33);
      REPEAT GetSym UNTIL sym >= lparen
    END;
    IF sym = array THEN
      GetSym; ArrayType(typ)
    ELSIF sym = record THEN
      GetSym; typ := NewStr(Record); NewScope(Typ);
      FieldListSequence(typ^.size, 0); typ^.firstFld := topScope^.next;
      typ^.size := VAL(INTEGER,VAL(CARDINAL,-typ^.size) MOD 2) + typ^.size; (*%*)
      CheckSym(end, 20); CloseScope
    ELSIF sym = set THEN
      GetSym; CheckSym(of, 23);
      typ := NewStr(Set); SimpleType(typ^.SBaseTyp);
      btyp := typ^.SBaseTyp;
      IF btyp^.form = Enum THEN
        IF btyp^.NofConst > WordSize THEN err(209) END
      ELSIF btyp^.form = Range THEN
        IF (btyp^.min < 0) OR (btyp^.max >= WordSize) THEN err(209) END
      ELSE err(60)
      END;
      typ^.size := SetTypSize
    ELSIF sym = pointer THEN
      GetSym; typ := NewStr(Pointer);
      typ^.BaseId := 0; typ^.size := PointerTypSize; CheckSym(to, 24);
      IF sym = ident THEN qualident(obj);
        IF obj = NIL THEN typ^.BaseId := id; KeepId (*forward ref*)
        ELSIF obj^.class = Typ THEN typ^.PBaseTyp := obj^.typ
        ELSE err(52)
        END
      ELSE Type(typ^.PBaseTyp)
      END
    ELSIF sym = procedure THEN
      GetSym; typ := NewStr(ProcTyp); typ^.size := ProcTypSize;
      IF sym = lparen THEN
        GetSym; FormalTypeList(typ)
      ELSE typ^.resTyp := notyp;
      END
    ELSE
      SimpleType(typ)
    END;
    IF (sym < semicolon) OR (else < sym) THEN err(34);
      WHILE (sym < ident) OR (else < sym) & (sym < begin) DO
        GetSym
      END
    END
  END Type;
  PROCEDURE selector(VAR x: Item; obj: ObjPtr);
    VAR y: Item;
  BEGIN GenItem(x, obj, Scope);
    LOOP
      IF sym = lbrak THEN GetSym;
        LOOP Expression(y); GenIndex(x, y);
          IF sym = comma THEN GetSym ELSE EXIT END
        END;
        CheckSym(rbrak, 16)
      ELSIF sym = period THEN
        GetSym;
        IF sym = ident THEN
          IF (x.typ # NIL) & (x.typ^.form = Record) THEN
            obj := FindInScope(id, x.typ^.firstFld); GenField(x, obj)
          ELSE err(57)
          END;
          GetSym
        ELSE err(10)
        END
      ELSIF sym = arrow THEN
        GetSym; GenDeRef(x)
      ELSE EXIT
      END
    END
  END selector;
  PROCEDURE ActualParameters(VAR x: Item; fpar: ParPtr);
    VAR apar: Item;
  BEGIN
    IF sym # rparen THEN
      LOOP Expression(apar);
        IF fpar # NIL THEN
          GenParam(apar, fpar); fpar := fpar^.next
        ELSE err(64)
        END;
        IF sym = comma THEN GetSym
        ELSIF (lparen <= sym) & (sym <= ident) THEN err(11); GetSym;
        ELSE EXIT
        END
      END
    END;
    IF fpar # NIL THEN err(65) END
  END ActualParameters;
  PROCEDURE StandProcCall(VAR p: Item);
    VAR x: Item; m: Standard; n: INTEGER;
  BEGIN m := p.proc^.std; n := 0;
    IF m = Halt THEN GenHalt(0); (* HALT *) ELSE
      CheckSym(lparen, 22);
      LOOP Expression(x); GenVal(x);
        GenStParam(p, x, m, n, sym = comma); INC(n);
        IF sym = comma THEN GetSym ELSIF sym # ident THEN EXIT END
      END;
      CheckSym(rparen, 15); GenStFct(m, n)
    END
  END StandProcCall;
  PROCEDURE Element(VAR x: Item);
    VAR e1, e2: Item;
  BEGIN Expression(e1); GenVal(e1);
    IF sym = ellipsis THEN
      GetSym; Expression(e2); GenVal(e2);
      GenSet(x, e1, e2)
    ELSE GenSingSet(x, e1)
    END;
  END Element;
  PROCEDURE Sets(VAR x: Item; styp: StrPtr);
    VAR y: Item;
  BEGIN x.typ := styp; y.typ := styp;
    IF sym # rbrace THEN
      Element(x);
      LOOP
        IF sym = comma THEN GetSym
        ELSIF (lparen <= sym) & (sym <= ident) THEN err(11)
        ELSE EXIT
        END;
        Element(y); GenOp(plus, x, y)
      END
    ELSE SetconMd(x, 0D, styp);
    END;
    CheckSym(rbrace, 17)
  END Sets;
  PROCEDURE Factor(VAR x: Item);
    VAR obj: ObjPtr; xt: StrPtr; fpar: ParPtr; savedRegs: LONGINT;
  BEGIN
    IF sym < lparen THEN err(31);
      REPEAT GetSym UNTIL sym >= lparen
    END;
    IF sym = ident THEN
      qualident(obj);
      IF sym = lbrace THEN
        GetSym;
        IF (obj # NIL) & (obj^.class = Typ) &
           (obj^.typ^.form = Set) THEN Sets(x, obj^.typ)
        ELSE err(52); Sets(x, bitstyp)
        END
      ELSE
        selector(x, obj);
        IF (x.mode = codMd) & (x.proc^.std # NonStand) THEN StandProcCall(x)
        ELSIF sym = lparen THEN GetSym;
          IF x.mode = typMd THEN
            (* type transfer functions are now deleted from Modula-2 ! *)
            err(260);
            xt := x.typ; Expression(x); ConvertTyp(xt, x);
            x.typ := xt;
          ELSE PrepCall(x, fpar, savedRegs);
            ActualParameters(x, fpar); GenCall(x, savedRegs);
          END;
          CheckSym(rparen, 15)
        END
      END
    ELSIF sym = number THEN
      GetSym;
      x.mode := conMd;
      CASE numtyp OF
        1: x.typ := cardtyp; x.val.C  := intval
      | 2: x.typ := dbltyp;  x.val.D  := dblval
      | 3: x.typ := chartyp; x.val.Ch := VAL(CHAR, intval)
      | 4: x.typ := realtyp; x.val.R  := realval
      | 5: x.typ := lrltyp;  x.val.X  := lrlval
      END
    ELSIF sym = string THEN
      x.typ := stringtyp; x.mode := conMd;
      AllocString(id, x.val.D0, x.val.D1); x.val.D2 := 0; GetSym
    ELSIF sym = lparen THEN
      GetSym; Expression(x); CheckSym(rparen, 15)
    ELSIF sym = lbrace THEN GetSym; Sets(x, bitstyp)
    ELSIF sym = not THEN
      GetSym; Factor(x); GenNot(x)
    ELSE err(31); SetregMd(x, 0, undftyp);
    END
  END Factor;
  PROCEDURE Term(VAR x: Item);
    VAR y: Item; mulop: Symbol;
  BEGIN Factor(x);
    WHILE (times <= sym) & (sym <= and) DO
      mulop := sym; GetSym;
      IF mulop = and THEN GenAnd(x) END;
      Factor(y); GenOp(mulop, x, y)
    END
  END Term;
  PROCEDURE SimpleExpression(VAR x: Item);
    VAR y: Item; addop: Symbol;
  BEGIN
    IF sym = minus THEN
      GetSym; Term(x); GenNeg(x)
    ELSE
      IF sym = plus THEN GetSym END;
      Term(x)
    END;
    WHILE (plus <= sym) & (sym <= or) DO
      addop := sym; GetSym;
      IF addop = or THEN GenOr(x) END;
      Term(y); GenOp(addop, x, y)
    END
  END SimpleExpression;
  PROCEDURE Expression(VAR x: Item);
    VAR y: Item; relation: Symbol;
  BEGIN SimpleExpression(x);
    IF (eql <= sym) & (sym <= in) THEN
      relation := sym; GetSym;
      GenVal(x);
      SimpleExpression(y);
      GenVal(y);
      IF relation = in THEN GenIn(x,y)
      ELSE GenOp(relation,x,y) END;
    END
  END Expression;
  PROCEDURE Priority;
    VAR x: Item;
  BEGIN
    IF sym = lbrak THEN
      GetSym; ConstExpression(x);
      IF (x.typ = cardtyp) & (x.val.C < 16) THEN curPrio := x.val.C
        ELSE err(147)
      END;
      CheckSym(rbrak, 16)
    ELSE curPrio := 0
    END
  END Priority;
  PROCEDURE ImportList(impmod: ObjPtr);
    VAR obj: ObjPtr;
  BEGIN
    IF (impmod # NIL) & (impmod^.class # Module) THEN
      err(55); impmod := NIL
    END;
    LOOP
      IF sym = ident THEN
        IF impmod = NIL THEN obj := FindImport(id)
        ELSE obj := FindInScope(id, impmod^.root);
          IF (obj # NIL) & NOT obj^.exported THEN obj := NIL END
        END;
        IF obj # NIL THEN NewImp(topScope, obj) ELSE err(50) END;
        GetSym
      ELSE err(10)
      END;
      IF sym = comma THEN GetSym
      ELSIF sym = ident THEN err(11)
      ELSE EXIT
      END
    END;
    CheckSym(semicolon, 12)
  END ImportList;
  PROCEDURE ExportList;
    VAR obj: ObjPtr;
  BEGIN
    LOOP
      IF sym = ident THEN
        obj := NewObj(id, Temp); KeepId; GetSym
      ELSE err(10)
      END;
      IF sym = comma THEN GetSym
      ELSIF sym = ident THEN err(11)
      ELSE EXIT
      END
    END;
    CheckSym(semicolon, 12)
  END ExportList;
  PROCEDURE Block(ancestor: ObjPtr; qual: BOOLEAN;
                  VAR adr: INTEGER; VAR L0: CARDINAL);
    VAR obj, last: ObjPtr; newtypdef: BOOLEAN;
        id0, s: INTEGER; x: Item; typ: StrPtr;
        L1, exits, loopLev, blockEnd: CARDINAL; exitTab: ExitTable;
  PROCEDURE ChangeAllRefs(opaS, newS: StrPtr);
    VAR mod: ObjPtr;
    PROCEDURE ChangeTyp(VAR t: StrPtr); FORWARD;
    PROCEDURE ChangeParams(first: ParPtr);
      VAR par: ParPtr;
    BEGIN par := first;
      WHILE par # NIL DO
        ChangeTyp(par^.typ); par := par^.next;
      END;
    END ChangeParams;
    PROCEDURE ChangeFields(first: ObjPtr);
      VAR obj: ObjPtr;
    BEGIN obj := first;
      WHILE obj # NIL DO
        ChangeTyp(obj^.typ); obj := obj^.next;
      END;
    END ChangeFields;
    PROCEDURE ChangeTyp(VAR t: StrPtr);
      VAR this: StrPtr;
    BEGIN this := t;
      IF this # NIL THEN
        WITH this^ DO
          CASE form OF
          | Pointer: IF PBaseTyp = opaS THEN PBaseTyp := newS END;
          | ProcTyp: ChangeParams(firstPar); ChangeTyp(resTyp);
          | Opaque:  IF this = opaS THEN t := newS END;
          | Array:   ChangeTyp(ElemTyp);
          | Record:  ChangeFields(firstFld);
          ELSE (* nothing to change for all other variants *)
          END;
        END;
      END;
    END ChangeTyp;
    PROCEDURE ChangeObjects(root: ObjPtr);
      VAR obj: ObjPtr;
    BEGIN obj := root;
      WHILE obj # NIL DO
        WITH obj^ DO
          CASE class OF
          | Header, Temp:
          | Const, Typ,
            Var, Field: ChangeTyp(typ); (* change object's main type *)
          | Proc:       ChangeParams(firstParam); ChangeTyp(typ);
          | Code:       ChangeParams(firstArg); ChangeTyp(typ);
          | Module:
          END;
        END;
        obj := obj^.next;
      END;
    END ChangeObjects;
  BEGIN
    mod := ModList^.next;
    WHILE mod # NIL DO ChangeObjects(mod^.firstObj); mod := mod^.next END;
    IF ancestor # mainmod THEN err(101) END;
  END ChangeAllRefs;
  PROCEDURE FormalParameters(proc: ObjPtr);
    VAR isvar: BOOLEAN; size: INTEGER;
        par, par0, par1: ParPtr; typ0: StrPtr;
  BEGIN par := NIL; size := 0;
    IF (sym = ident) OR (sym = var) THEN
      LOOP par1 := par; isvar := FALSE;
        IF sym = var THEN GetSym; isvar := TRUE END;
        LOOP
          IF sym = ident THEN
            par := NewPar(id, isvar, par); KeepId; GetSym
          ELSE err(10)
          END;
          IF sym = comma THEN GetSym
          ELSIF sym = ident THEN err(11)
          ELSIF sym = var THEN err(11); GetSym
          ELSE EXIT
          END
        END;
        CheckSym(colon, 13); FormalType(typ0); par0 := par;
        WHILE par0 # par1 DO
          par0^.typ := typ0; AllocPar(par0, size); par0 := par0^.next;
        END;
        IF sym = semicolon THEN GetSym
        ELSIF sym = ident THEN err(12)
        ELSE EXIT
        END
      END
    END;
    par1 := NIL; (*reverse list*)
    WHILE par # NIL DO
      par0 := par; par := par0^.next; par0^.next := par1; par1 := par0
    END;
    proc^.firstParam := par1; proc^.pd^.size := ABS(size); (*of param area*)
    CheckSym(rparen, 15)
  END FormalParameters;
  PROCEDURE CheckParameters(proc: ObjPtr);
    VAR isvar: BOOLEAN;
        par, par0, par1: ParPtr; typ0: StrPtr;
  BEGIN par0 := proc^.firstParam;
    IF (sym = ident) OR (sym = var) THEN
      LOOP par1 := par0; isvar := FALSE;
        IF sym = var THEN GetSym; isvar := TRUE END;
        LOOP
          IF sym = ident THEN
            IF par0 # NIL THEN par0^.name := id; par0 := par0^.next
              ELSE err(66)
            END;
            KeepId; GetSym
          ELSE err(10)
          END;
          IF sym = comma THEN GetSym
          ELSIF sym = ident THEN err(11)
          ELSIF sym = var THEN err(11); GetSym
          ELSE EXIT
          END
        END;
        CheckSym(colon, 13); FormalType(typ0); par := par1;
        WHILE par # par0 DO
          IF (par^.typ # typ0) &
            ((par^.typ^.form # Array) OR (typ0^.form # Array) OR
             (par^.typ^.ElemTyp # typ0^.ElemTyp)) THEN err(69)
          END;
          IF par^.varpar # isvar THEN err(68) END;
          par := par^.next
        END;
        IF sym = semicolon THEN GetSym
        ELSIF sym = ident THEN err(12)
        ELSE EXIT
        END
      END
    END;
    IF par0 # NIL THEN err(70) END;
    CheckSym(rparen, 15)
  END CheckParameters;
  PROCEDURE MakeParameterObjects(proc: ObjPtr);
    VAR par: ParPtr; obj: ObjPtr; adr: INTEGER;
  BEGIN par := proc^.firstParam;
    IF curLev = 1 THEN
      adr := GlbParStartAdr + proc^.pd^.size;
    ELSE
      adr := LocParStartAdr + proc^.pd^.size;
    END;
    WHILE par # NIL DO
      obj := NewObj(par^.name, Var); (*name field no longer used*)
      WITH obj^ DO
        typ := par^.typ; vmod := 0; vlev := curLev; varpar := par^.varpar;
        AllocPar(par, adr); vadr := adr;
      END;
      par := par^.next
    END
  END MakeParameterObjects;
  PROCEDURE ProcedureDeclaration(VAR proc: ObjPtr);
    VAR i, L0, L1: CARDINAL; adr: INTEGER; par, res: ObjPtr;
  BEGIN
    proc := Find(id);
    IF (proc # NIL) & (proc^.class = Proc) & (proc^.pmod = 0) &
       ((proc^.pd^.adr = 0) & (curLev = 0) & isimp OR (*heading in def mod *)
        proc^.pd^.forward & (proc^.pd^.lev = VAL(INTEGER,curLev))) THEN (*forward*)
      IF proc^.pd^.adr = 0 THEN proc^.pd^.exp := TRUE END;
      CheckSym(ident, 10);
      IF sym = lparen THEN
        GetSym; CheckParameters(proc);
        IF sym = colon THEN GetSym;
          IF sym = ident THEN qualident(res);
            IF (res = NIL) OR (res^.class # Typ) OR (res^.typ # proc^.typ) THEN
              err(71)
            END
          ELSE err(10)
          END
        ELSIF proc^.typ # notyp THEN err(72)
        END
      ELSIF proc^.firstParam # NIL THEN err(73)
      END
    ELSE (*new procedure*)
      proc := NewObj(id, Proc); KeepId;
      WITH proc^ DO
        pmod := 0; typ := notyp; firstParam := NIL;
      END;
      WITH proc^.pd^ DO
        forward := FALSE; exp := FALSE;
        lev := curLev; adr := 0; size := 0; INC(pno); num := pno;
      END;
      CheckSym(ident, 10);
      IF sym = lparen THEN
        GetSym; FormalParameters(proc);
        IF sym = colon THEN
          GetSym; proc^.typ := undftyp;
          IF sym = ident THEN qualident(res);
            IF (res # NIL) & (res^.class = Typ) THEN proc^.typ := res^.typ
            ELSE err(52)
            END
          ELSE err(10)
          END
        END
      END
    END;
    CheckSym(semicolon, 12);
    IF sym = code THEN
      GetSym; DEC(pno);
      WITH proc^ DO
        IF pd^.exp OR pd^.forward THEN err(74) END;
        class := Code; std := NonStand; ConstExpression(x);
        IF x.typ = cardtyp THEN cnum := x.val.C
        ELSE cnum := 0; err(133)
        END;
      END;
      CheckSym(semicolon, 12);
    ELSIF NOT isdef THEN
      i := proc^.pd^.adr;
      MarkHeap; NewScope(Proc); INC(curLev);
      IF sym = forward THEN GetSym;
        WITH proc^.pd^ DO
          IF exp OR forward THEN err(74) END;
          forward := TRUE; exp := FALSE;
          lev := curLev-1; GenFJ(i); adr := i-2;
        END;
        (*MakeParameterObjects(proc)*)
      ELSE MakeParameterObjects(proc);
        IF proc^.pd^.forward THEN fixup(i+2) END;
        proc^.pd^.adr := pc; proc^.pd^.forward := FALSE;
        L0 := 0; GenEnter(L1, proc^.pd^.lev); GenFJ(L0);
        adr := LocVarStartAdr; Block(proc, FALSE, adr, L0); FixupWith(L1, adr);
      END;
      DEC(curLev); CloseScope; ReleaseHeap; CheckSym(semicolon, 12);
    END
  END ProcedureDeclaration;
  PROCEDURE ModuleDeclaration(VAR mod: ObjPtr; VAR adr: INTEGER; VAR L0: CARDINAL);
    VAR prio: INTEGER; qual: BOOLEAN; impmod: ObjPtr;
  BEGIN qual := FALSE; CheckSym(ident, 10);
    mod := NewObj(id, Module); KeepId;
    INC(mno); mod^.modno := mno; prio := curPrio; Priority;
    CheckSym(semicolon, 12); NewScope(Module);
    WHILE (sym = from) OR (sym = import) DO impmod := NIL;
      IF sym = from THEN GetSym;
        IF sym = ident THEN
          impmod := FindImport(id); GetSym
        ELSE err(10)
        END;
        CheckSym(import, 30)
      ELSE GetSym
      END;
      ImportList(impmod)
    END;
    IF sym = export THEN GetSym;
      IF sym = qualified THEN GetSym; qual := TRUE END;
      ExportList
    END;
    Block(mod, qual, adr, L0);
    CloseScope; curPrio := prio
  END ModuleDeclaration;
  PROCEDURE StatSeq;
    VAR obj: ObjPtr; fpar: ParPtr; x, y: Item; L0, L1, s, e: CARDINAL;
        savedRegs: LONGINT;
    PROCEDURE CasePart;
      VAR x: Item; n: INTEGER; L0, L1: CARDINAL;
          tab: ARRAY [0..NofCases-1] OF LabelRange;
    BEGIN n := 0;
      Expression(x); GenCase1(x, L0); CheckSym(of, 23);
      LOOP
        IF sym < bar THEN
          CaseLabelList(x.typ, n, tab);
          CheckSym(colon, 13); StatSeq; GenCase2
        END;
        IF sym = bar THEN GetSym ELSE EXIT END
      END;
      L1 := pc;
      IF sym = else THEN
        GetSym; StatSeq; GenCase2
      ELSE GenHalt(1); GenCase2
      END;
      RefPoint; GenCase3(x, L0, L1, n, tab)
    END CasePart;
    PROCEDURE ForPart;
      VAR obj: ObjPtr;
          v, e1, e2, e3: Item;
          L0, L1: CARDINAL;
    BEGIN obj := NIL;
      IF sym = ident THEN
        obj := Find(id);
        IF obj # NIL THEN
          IF (obj^.class # Var) OR obj^.varpar OR (obj^.vmod > 0) THEN err(75) END
        ELSE err(50)
        END;
        GetSym
      ELSE err(10)
      END;
      GenItem(v, obj, Scope);
      IF sym = becomes THEN GetSym ELSE err(19);
        IF sym = eql THEN GetSym END
      END;
      Expression(e1); GenVal(e1); GenFor1(v, e1);
      CheckSym(to,24); Expression(e2); GenVal(e2); GenFor2(v, e1, e2);
      IF sym = by THEN
        GetSym; ConstExpression(e3)
      ELSE SetconMd(e3, 1D, cardtyp);
      END;
      GenFor3(v, e2, e3, L0, L1);
      CheckSym(do, 25); StatSeq; GenFor4(v, e2, e3, L0, L1)
    END ForPart;
  BEGIN
    LOOP
      IF sym < ident THEN err(35);
        REPEAT GetSym UNTIL sym >= ident
      END;
      IF sym = ident THEN
        RefPoint; qualident(obj); selector(x, obj);
        IF sym = becomes THEN
          GetSym; Expression(y); GenAssign(x, y)
        ELSIF sym = eql THEN
          err(19); GetSym; Expression(y); GenAssign(x, y)
        ELSIF (x.mode = codMd) & (x.proc^.std # NonStand) THEN
          StandProcCall(x);
          IF x.typ # notyp THEN err(76) END
        ELSE PrepCall(x, fpar, savedRegs);
          IF sym = lparen THEN
            GetSym; ActualParameters(x, fpar); CheckSym(rparen, 15)
          ELSIF fpar # NIL THEN err(65)
          END;
          GenCall(x, savedRegs);
          IF x.typ # notyp THEN err(76) END
        END
      ELSIF sym = if THEN
        GetSym; RefPoint; Expression(x); GenCFJ(x, L0);
        CheckSym(then, 27); StatSeq; L1 := 0;
        WHILE (sym = elsif) DO
          GetSym; GenFJ(L1); FixLink(L0); RefPoint; Expression(x);
          GenCFJ(x, L0); CheckSym(then, 27); StatSeq
        END;
        IF sym = else THEN
          GetSym; GenFJ(L1); FixLink(L0); StatSeq
        ELSE FixLink(L0)
        END;
        FixLink(L1); CheckSym(end, 20)
      ELSIF sym = case THEN
        GetSym; RefPoint; CasePart; CheckSym(end, 20)
      ELSIF sym = while THEN
        GetSym; L1 := pc; RefPoint; Expression(x); GenCFJ(x, L0);
        CheckSym(do, 25); StatSeq; GenBJ(L1); FixLink(L0);
        CheckSym(end, 20)
      ELSIF sym = repeat THEN
        GetSym; L0 := pc; StatSeq;
        IF sym = until THEN
          GetSym; RefPoint; Expression(x); GenCBJ(x, L0)
        ELSE err(26)
        END
      ELSIF sym = loop THEN
        GetSym; INC(loopLev); GenLoop1(s, e, exits);
        L0 := pc; StatSeq; GenBJ(L0); CheckSym(end, 20);
        GenLoop2(s, e, exits, exitTab); DEC(loopLev);
      ELSIF sym = for THEN
        GetSym; RefPoint; ForPart; CheckSym(end, 20)
      ELSIF sym = with THEN
        GetSym; x.typ := NIL;
        IF sym = ident THEN
          qualident(obj); selector(x, obj);
          IF x.typ^.form = Record THEN
            NewScope(Typ); GenWith(x, adr); topScope^.name := wlev;
            topScope^.right := x.typ^.firstFld;
          ELSE err(57); x.typ := NIL
          END
        ELSE err(10)
        END;
        CheckSym(do, 25); StatSeq; CheckSym(end, 20);
        IF x.typ # NIL THEN CloseScope END;
        GenWith2;
      ELSIF sym = exit THEN
        GetSym;
        IF loopLev > 0 THEN GenExit(exits, exitTab) ELSE err(39) END;
      ELSIF sym = return THEN GetSym;
        IF sym < semicolon THEN Expression(x)
        ELSE
          x.typ := notyp;
          IF ancestor^.typ # notyp THEN err(139) END;
        END;
        GenResult(x, ancestor, blockEnd)
      END;
      CheckRegs;
      IF sym = semicolon THEN GetSym
      ELSIF (sym <= ident) OR (if <= sym) & (sym <= for) THEN err(12)
      ELSE EXIT
      END
    END
  END StatSeq;
  PROCEDURE CheckExports(obj: ObjPtr);
  BEGIN
    IF obj # NIL THEN
      IF obj^.class = Temp THEN Mark(80)
      ELSIF ~qual & obj^.exported THEN (*import in outer scope*)
        NewImp(topScope^.left, obj)
      END;
      CheckExports(obj^.left); CheckExports(obj^.right)
    END
  END CheckExports;
  PROCEDURE CheckUDProc(obj: ObjPtr);
  BEGIN (*check for undefined procedure bodies*)
    WHILE obj # NIL DO
      IF (obj^.class = Proc) & (obj^.pmod = 0) &
         ((obj^.pd^.adr = 0) OR obj^.pd^.forward) THEN err(89)
      END;
      obj := obj^.next
    END
  END CheckUDProc;
  BEGIN (*Block*)
    LOOP
      IF sym = const THEN
        GetSym;
        WHILE sym = ident DO
          id0 := id; KeepId; GetSym;
          IF sym = eql THEN
            GetSym; ConstExpression(x)
          ELSIF sym = becomes THEN
            err(18); GetSym; ConstExpression(x)
          ELSE err(18)
          END;
          obj := NewObj(id0, Const); obj^.typ := x.typ; obj^.conval := x.val;
          IF (x.typ = stringtyp) & (obj^.conval.D2 = 0) THEN
            obj^.conval.D2 := id; KeepId
          END;
          CheckSym(semicolon, 12)
        END
      ELSIF sym = type THEN
        GetSym;
        WHILE sym = ident DO
          typ := undftyp; obj := NIL; newtypdef := TRUE;
          IF isimp & (curLev = 0) THEN
            obj := Find(id);
            IF (obj # NIL) & (obj^.class = Typ) & (obj^.typ^.form = Opaque) THEN
              newtypdef := FALSE
            END
          END;
          IF newtypdef THEN id0 := id; KeepId END;
          GetSym;
          IF sym = eql THEN
            GetSym; Type(typ)
          ELSIF (sym = becomes) OR (sym = colon) THEN
            err(18); GetSym; Type(typ)
          ELSIF NOT isdef THEN err(18)
          ELSE typ := NewStr(Opaque); typ^.size := PointerTypSize
          END;
          IF newtypdef THEN
            obj := NewObj(id0, Typ); obj^.typ := typ; obj^.mod := mainmod;
            IF typ^.strobj = NIL THEN typ^.strobj := obj END;
          ELSIF typ^.size = PointerTypSize THEN ChangeAllRefs(obj^.typ, typ)
          ELSE err(101)
          END;
          CheckUDP(obj, topScope^.right); (* check for undefined pointer types *)
          CheckSym(semicolon, 12)
        END
      ELSIF sym = var THEN
        GetSym;
        WHILE sym = ident DO last := topScope^.last; obj := last;
          LOOP
            IF sym = ident THEN
              obj := NewObj(id, Var); KeepId; GetSym
            ELSE err(10)
            END;
            IF sym = comma THEN GetSym
            ELSIF sym = ident THEN err(11)
            ELSE EXIT
            END
          END;
          CheckSym(colon, 13); Type(typ);
          WHILE (last # obj) & (last # NIL) DO
            last := last^.next;
            IF last = NIL THEN last := obj END;
            last^.typ := typ;
            WITH last^ DO
              varpar := FALSE; vmod := 0; vlev := curLev;
            END;
            AllocVar(last, adr);
          END;
          CheckSym(semicolon, 12)
        END
      ELSIF sym = procedure THEN
        GetSym; ProcedureDeclaration(obj)
      ELSIF sym = module THEN
        GetSym; ModuleDeclaration(obj, adr, L0); CheckSym(semicolon, 12);
        GenFJ(L0)
      ELSE
        IF (sym # begin) & (sym # end) THEN err(36);
          REPEAT GetSym UNTIL (sym >= begin) OR (sym = end)
        END;
        IF (sym <= begin) OR (sym = eof) THEN EXIT END
      END
    END;
    exits := 0; loopLev := 0; blockEnd := 0;  (* label used in RETURN *)
    IF NOT isdef THEN
      IF pc - L0 = 2 THEN pc := pc - 4 ELSE fixup(L0) END;
    END;
    IF ancestor^.class = Module THEN
      CheckExports(topScope^.right);
      ancestor^.firstObj := topScope^.next; ancestor^.root := topScope^.right
    ELSE (*procedure*)
      ancestor^.firstLocal := topScope^.next;
      obj := topScope^.next;
      WHILE obj # NIL DO
        IF (obj^.typ^.form = Array) & obj^.typ^.dyn & NOT obj^.varpar THEN
          CopyDynArray(obj^.vadr, obj^.typ^.ElemTyp^.size)
        END;
        obj := obj^.next
      END;
    END;
    IF NOT isdef THEN CheckUDProc(topScope^.next) END;
    IF sym = begin THEN
      IF isdef THEN err(37) END;
      GetSym; StatSeq; RefPoint
    END;
    (*IF ancestor^.class = Proc THEN*)
      GenReturn(ancestor, blockEnd);
      IF (ancestor^.class = Proc) & NOT isdef THEN
        ancestor^.pd^.size := VAL(INTEGER,pc) - ancestor^.pd^.adr
      END;
    (*END;*)
    CheckSym(end, 20); IF NOT scanerr THEN OutUnit(ancestor) END;
    IF sym = ident THEN
      IF Diff(id, ancestor^.name) # 0 THEN err(77) END;
      GetSym
    ELSE err(10)
    END
  END Block;
  PROCEDURE CompilationUnit;
    VAR id0, adr: INTEGER; L0: CARDINAL;
        hdr, importMod: ObjPtr; impok, ok: BOOLEAN;
        FName, TName: ARRAY [0..NL] OF CHAR;
        p: Path; f: File; i: INTEGER; path1: Path;
    PROCEDURE GetFileName(j: INTEGER;
              VAR FName: ARRAY OF CHAR; ext: ARRAY OF CHAR);
      VAR i, L: INTEGER;
    BEGIN i := 0; L := VAL(INTEGER,ORD(IdBuf[j])) + j - 1;
      WHILE j < L DO
        INC(j); FName[i] := IdBuf[j]; INC(i)
      END;
      j := 0; L := HIGH(ext);
      WHILE j <= L DO
       FName[i] := ext[j]; INC(i); INC(j)
      END;
      FName[i] := 0C
    END GetFileName;
    PROCEDURE ImportModule;
      VAR adr, pno, i: INTEGER; f: File; p: Path; ok: BOOLEAN;
    BEGIN
      IF sym = ident THEN
        IF Diff(id, sysmod^.name) = 0 THEN importMod := sysmod
        ELSE
          GetFileName(id, FileName, ".SBM");
          InRef(FileName, hdr, adr, pno);
          WriteLn; WriteString(" - "); WriteString(FileName);
          IF hdr # NIL THEN importMod := hdr^.right
          ELSE impok := FALSE;
            importMod := NIL; WriteString(" not found (or bad)")
          END
        END;
        GetSym
      ELSE err(10)
      END;
    END ImportModule;
    PROCEDURE Out(n: INTEGER);
      VAR k: INTEGER;
          d: ARRAY [0..5] OF INTEGER;
    BEGIN k := 0; Write(" ");
      REPEAT d[k] := n MOD 10; n := n DIV 10; INC(k) UNTIL n = 0;
      REPEAT DEC(k); Write(VAL(CHAR,d[k]+60B)) UNTIL k = 0
    END Out;
  BEGIN isdef := FALSE; isimp := FALSE; impok := TRUE;
    curLev := 0; curPrio := 0; mno := 0;
    (*FName := "DK.";*) GetSym;
    IF sym = definition THEN GetSym; isdef := TRUE
    ELSIF sym = implementation THEN GetSym; isimp := TRUE
    END;
    IF sym = module THEN
      GetSym;
      IF sym = ident THEN
        id0 := id; mainmod^.name := id0; KeepId; GetSym;
        IF NOT isdef THEN Priority END;
        CheckSym(semicolon, 12); MarkHeap; NewScope(Module);
        IF isimp THEN
          GetFileName(id0, FName, ".SBM");
          InRef(FName, hdr, adr, pno);
          WriteLn; WriteString(" - "); WriteString(FName);
          IF hdr # NIL THEN importMod := hdr^.right;
               topScope^.right := importMod^.root;  (*mainmod*)
               topScope^.next := hdr^.next; topScope^.last := hdr^.last
          ELSE importMod := NIL;
            WriteString(" not found (or bad)"); impok := FALSE
          END
        ELSE adr := GlbVarStartAdr; pno := 0; mainmod^.key := sysmod^.key
        END;
        WHILE (sym = from) OR (sym = import) DO
          IF sym = from THEN
            GetSym; ImportModule; CheckSym(import, 30);
            ImportList(importMod)
          ELSE (*sym = import*) GetSym;
            LOOP ImportModule;
              IF importMod # NIL THEN NewImp(topScope, importMod) END;
              IF sym = comma THEN GetSym
              ELSIF sym # ident THEN EXIT
              END
            END;
            CheckSym(semicolon, 12)
          END
        END;
        IF sym = export THEN
          GetSym; err(38);
          WHILE sym # semicolon DO GetSym END;
          GetSym
        END;
        IF impok THEN
          IF isdef THEN
            GetFileName(id0, FName, ".SBM");
          ELSE
            GetFileName(id0, FName, ".RFM");
            GenEnterMod(ModList, ModNo, pno); L0 := 0; GenFJ(L0)
          END;
          AddPath(path, FName, TName);
          WriteLn;
          ExtLookup(RefFile, TName, TRUE, ok);
          IF ok THEN
            GetCurrentPath(path1);
            WriteString(" + "); WriteString(path1); WriteString(FName);
          ELSE
            WriteString(" + "); WriteString(FName); WriteString(" not opened")
          END;
          OpenRef; Block(mainmod, TRUE, adr, L0);
          IF sym # period THEN err(14) END;
          IF NOT scanerr THEN
            IF NOT isdef THEN
              GenExitMod;
              GetFileName(id0, FName, ".OBM"); AddPath(path, FName, TName);
              WriteLn; WriteString(" + ");
              OutCodeFile(TName, mainmod^.key, ABS(adr), pno, id0, ModList);
              GetCurrentPath(path1);
              WriteString(path1); WriteString(FName); Out(pc);
            END;
            CloseRef(adr, pno); Close(RefFile);
            IF RefFile.res = notdone THEN err(223) END;
          ELSE Delete(RefFile)
          END
        END;
        CloseScope; ReleaseHeap
      ELSE err(10)
      END;
    ELSE err(28)
    END;
    IF scanerr THEN WriteString(" errors detected") END
  END CompilationUnit;
BEGIN
  ProcessorID(processor); WriteString(processor);
  WriteString(" Modula-2 Compiler V2.6.7."); WriteLn;
  WriteString("ETH Zuerich, NW/HS/WH, 29-May-92."); WriteLn;
  Lookup(source, 'err.DAT', FALSE); FileName[0] := 0C;
  IF source.res = done THEN
    LOOP ReadChar(source, ch);
      IF ch = 300C THEN i := 0;
        REPEAT ReadChar(source, ch); FileName[i] := ch; INC(i) UNTIL ch = 0C;
      ELSE EXIT;
      END;
    END;
    Close(source);
  END;
  LOOP rngchk := TRUE; ovflchk := FALSE;
    WriteString("in> ");
    ReadFileName(FileName, "MOD", "TEXT", BusyRead, Write, ok);
    IF NOT ok THEN EXIT END;
    IF termCh = "/" THEN Write("/");
      LOOP Read(ch); ch := CAP(ch);
        IF ch = "R" THEN Write(ch); rngchk := FALSE
        ELSIF ch = "V" THEN Write(ch); ovflchk := TRUE
        ELSIF ch <= " " THEN EXIT
        ELSE Write("?")
        END
      END
    END;
    ExtLookup(source, FileName, FALSE, ok);
    IF ok THEN
      GetCurrentPath(path);
      AddPath(path, FileName, FileName);
      GetTime(TM);
      WITH sysmod^.key^ DO
        k0 := VAL(INTEGER, TM.day); k1 := VAL(INTEGER, TM.minute);
        k2 := VAL(INTEGER, TM.millisecond);
      END;
      InitScanner(FileName); InitTableHandler; InitRef;
      InitM2LM; InitM2HM; InitM2EM;
      CompilationUnit; Close(source);
    ELSE WriteString(" -- not found");
    END;
    WriteLn; FileName[0] := 0C;
  END;
  CloseScanner; WriteLn;
END Compile. (* Copyright Departement Informatik, ETH Zuerich, Switzerland, 1992 *)
