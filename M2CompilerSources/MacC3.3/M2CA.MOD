IMPLEMENTATION MODULE M2CA; (* HS 19.4.85 / 10.6.86 / 29.2.92; WH 9.5.85 / 27.6.85 *)
  FROM SYSTEM IMPORT WORD;
  FROM M2DA IMPORT
    WordSize, MaxInt, MaxDouble, ObjPtr, StrPtr, ParPtr, PDPtr,
    Standard, ObjClass, StrForm, PDesc, Object, ovflchk,
    notyp, undftyp, booltyp, chartyp, inttyp,
    bitstyp, dbltyp, realtyp, lrltyp, proctyp,
    stringtyp, addrtyp, bytetyp, wordtyp;
  FROM M2SA IMPORT
    Mark;
  FROM M2HA IMPORT
    D0, D1, SB, MP, SP,
    byte, word, long,
    Condition, RegType, Register, WidType, ItemMode, Item,
    LongVal, WordVal, SimpleT, RealT,
    GetReg, Release, ReleaseReg, SetbusyReg, SaveRegs, RestoreRegs,
    SetlocMd, SetregMd, SetstkMd, SetconMd,
    StackTop, SetupSL, GenHalt,
    LoadD, LoadP, LoadX, Move, MoveAdr, MoveBlock, Tst1, Add2, Cmp2,
    CheckClimit, CheckRange, DynArray,
    Jf, Jb, EnterCase, ExitCase, Link, Unlink, CallInt, CallExt, CallInd,
    EnterModule, ExitModule, InitModule,
    FMove, LoadF, FMonad;
  FROM M2LA IMPORT
    pc, maxP, maxM, PutWord, AllocChar, FixLink, FixLinkWith, fixup;
  FROM M2EA IMPORT
    GlbParStartAdr, LocParStartAdr;
  VAR sp0, sp : INTEGER;
  PROCEDURE err(n: INTEGER);
    (* local synonym for M2SM.Mark to save space! *)
  BEGIN
    Mark(n);
  END err;
  PROCEDURE Put16(w : WORD);
    (* local synonym for M2LM.PutWord to save space! *)
  BEGIN
    PutWord(w);
  END Put16;
  PROCEDURE SRTest(VAR x : Item);
  BEGIN
    WITH x DO
      WHILE typ^.form = Range DO typ := typ^.RBaseTyp END;
    END (*WITH*);
  END SRTest;
  PROCEDURE setCC(VAR x : Item; fcc : Condition);
    (* transform all modes to 'cocMd' : *)
  BEGIN
    Release(x);
    WITH x DO
      typ := booltyp; mode := cocMd; CC := fcc;
      Tjmp := 0; Fjmp := 0;
    END;
  END setCC;
  PROCEDURE GenAssign(VAR x, y : Item);
    (*       x    :=    y     *)
    (*       y  ---->>  x     *)
    (* or    g  ---->>  f     *)
    VAR f, g     : StrForm;
        xp, yp   : ParPtr;
        x0, y0   : Item;
        s, sadr  : INTEGER;
        Min, Max : INTEGER;
        L        : INTEGER;
        sz       : WidType;
        xt       : StrPtr;
  BEGIN
    IF (x.mode = conMd) OR (x.mode > stkMd) THEN err(134) END;
    SRTest(y);
    f := x.typ^.form;
    g := y.typ^.form;
    xt := x.typ; (* hold original type of x *)
    IF f = Range THEN
      (* perform range check. *)
      Min := x.typ^.min; Max := x.typ^.max;
      IF y.mode = conMd THEN
        IF (LongVal(y) < LONG(Min)) OR (LongVal(y) > LONG(Max)) THEN
          err(138)
        END
      ELSE
        CheckRange(y, Min, Max, 0)
      END;
      x.typ := x.typ^.RBaseTyp;
      f := x.typ^.form;
    END (*Range*);
    CASE f (* destination form *) OF
      Undef :    err(133);
    | Byte :     IF y.typ^.size = 1 THEN Move(y,x)
                 ELSE err(133)
                 END;
    | Bool :     IF g = Bool THEN Move(y,x)
                 ELSE err(133)
                 END;
    | Char :     IF g = Char THEN Move(y,x)
                 ELSIF g = Byte THEN Move(y,x)
                 ELSE err(133)
                 END;
    | Int :      IF g = Int THEN Move(y,x)
                 ELSE err(133)
                 END;
    | Enum :     IF x.typ = y.typ THEN Move(y,x)
                 ELSE err(133)
                 END;
    | Word :     IF y.typ^.size = 2 THEN Move(y,x)
                 ELSE err(133)
                 END;
    | LWord :    IF g = LWord THEN Move(y,x)
                 ELSIF g = Double (* double constants *) THEN Move(y,x)
                 ELSIF (x.typ = addrtyp) & (g = Pointer) THEN Move(y,x)
                 ELSIF g = Int THEN
                   IF y.mode = conMd THEN
                     SetconMd(y, LongVal(y), xt);
                   ELSE
                     LoadX(y,long); y.typ := xt;
                   END;
                   Move(y,x)
                 ELSE err(133)
                 END;
    | Double :   IF g = Double THEN Move(y,x)
                 ELSIF g = Int THEN
                   IF y.mode = conMd THEN
                     SetconMd(y, LongVal(y), xt);
                   ELSE
                     LoadX(y,long); y.typ := xt;
                   END;
                   Move(y,x)
                 ELSE err(133)
                 END;
    | Real :     IF g = Real THEN FMove(y,x)
                 ELSE err(133)
                 END;
    | LongReal : IF g = LongReal THEN FMove(y,x)
                 ELSIF g = Real THEN
                   FMonad(Long,y);
                   y.typ := xt;
                   FMove(y,x)
                 ELSE err(133)
                 END;
    | Pointer :  IF (x.typ = y.typ) OR (y.typ = addrtyp) THEN
                   Move(y,x)
                 ELSE err(133)
                 END;
    | Set :      IF x.typ = y.typ THEN Move(y,x)
                 ELSE err(133)
                 END;
    | Opaque :   IF (x.typ = y.typ) THEN Move(y,x)
                 ELSE err(133)
                 END;
    | Record :   IF x.typ = y.typ THEN
                   s := x.typ^.size;
                   MoveBlock(y,x,s,FALSE)
                 ELSE err(133)
                 END;
    | ProcTyp :  IF y.mode = procMd THEN
                   (* procedure-constant to procedure-variable : *)
                   IF y.proc^.pd^.lev # 0 THEN err(127)
                   ELSIF x.typ^.resTyp # y.proc^.typ THEN err(128)
                   ELSE xp := x.typ^.firstPar; yp := y.proc^.firstParam;
                     WHILE xp # NIL DO
                       IF yp # NIL THEN
                         IF (xp^.varpar # yp^.varpar) OR
                            ((xp^.typ # yp^.typ) AND
                            ((xp^.typ^.form # Array) OR
                             NOT xp^.typ^.dyn OR
                             (yp^.typ^.form # Array) OR
                             NOT yp^.typ^.dyn OR
                             (xp^.typ^.ElemTyp # yp^.typ^.ElemTyp))) THEN
                           err(129)
                         END;
                         yp := yp^.next
                       ELSE err(130)
                       END;
                       xp := xp^.next
                     END (*WHILE*);
                     IF yp # NIL THEN err(131) END;
                     MoveAdr(y,x);
                   END;
                 ELSIF x.typ = y.typ THEN Move(y,x)
                 ELSE err(133)
                 END;
    | Array :    s := x.typ^.size;
                 IF (x.typ = y.typ) & NOT(x.typ^.dyn) THEN
                   MoveBlock(y,x,s,FALSE)
                 ELSIF (x.mode = stkMd) & x.typ^.dyn THEN
                   (* formal parameter is dynamic array : *)
                   IF (g = Array) & (x.typ^.ElemTyp = y.typ^.ElemTyp) THEN
                     DynArray(x,y)
                   ELSE
                     IF (x.typ^.ElemTyp = chartyp) OR
                        (x.typ^.ElemTyp = bytetyp) THEN
                       IF g = String THEN
                         DynArray(x,y)
                       ELSIF (g = Char) & (y.mode = conMd) THEN
                         (* character-constant to dynamic array : *)
                         AllocChar(y.val.Ch, sadr);
                         WITH y DO
                           typ := stringtyp; val.D0 := sadr; val.D1 := 2;
                         END (*WITH*);
                         DynArray(x,y)
                       ELSIF (x.typ^.ElemTyp = bytetyp) THEN DynArray(x,y)
                       ELSE err(133)
                       END
                     ELSE err(133)
                     END
                   END
                 ELSIF (x.typ^.ElemTyp = chartyp) THEN
                   IF x.typ^.dyn THEN err(143) END;
                   IF x.typ^.IndexTyp # NIL THEN
                     WITH x.typ^.IndexTyp^ DO
                       IF form = Range THEN s := max - min + 1 END;
                     END;
                   END;
                   IF g = String THEN
                     (* string to fixed-size array : 4th edition *)
                     (* length of string must be less than that of array! *)
                     IF y.val.D1 > s THEN err(146) END;
                     MoveBlock(y,x,s,TRUE);
                   ELSIF (g = Char) & (y.mode = conMd) THEN
                     (* character-constant to fixed-size array : *)
                     AllocChar(y.val.Ch, sadr);
                     WITH y DO
                       typ := stringtyp; val.D0 := sadr; val.D1 := 2;
                     END (*WITH*);
                     IF s < 2 THEN err(146) END;
                     MoveBlock(y,x,s,TRUE);
                   ELSE err(133)
                   END
                 ELSE err(133)
                 END;
    ELSE (* must not occur on the left side *)
      err(133)
    END (*CASE f*);
    x.typ := xt; (* restore original type of x *)
    Release(y);
    Release(x);
  END GenAssign;
  PROCEDURE GenFJ(VAR loc: INTEGER);
  BEGIN
    Jf(T, loc);
  END GenFJ;
  PROCEDURE GenCFJ(VAR x: Item; VAR loc: INTEGER);
  BEGIN
    IF x.typ = booltyp THEN
      IF x.mode # cocMd THEN Tst1(x); setCC(x, EQ) END;
    ELSE
      setCC(x, EQ); err(135);  (* type of expression must be boolean *)
    END;
    loc := x.Fjmp; Jf(x.CC, loc); FixLink(x.Tjmp);
  END GenCFJ;
  PROCEDURE GenBJ(loc: INTEGER);
  BEGIN
    Jb(T, loc);
  END GenBJ;
  PROCEDURE GenCBJ(VAR x: Item; loc: INTEGER);
  BEGIN
    IF x.typ = booltyp THEN
      IF x.mode # cocMd THEN Tst1(x); setCC(x, EQ) END;
    ELSE
      setCC(x, EQ); err(135);  (* type of expression must be boolean *)
    END;
    Jb(x.CC, loc); FixLinkWith(x.Fjmp, loc); FixLink(x.Tjmp);
  END GenCBJ;
  PROCEDURE SpaceForFunction(func : StrPtr);
    (* reserve space on top of stack for function result. *)
    VAR tos : Item;
  BEGIN
    SetstkMd(tos, func);
    IF SimpleT(tos) OR RealT(tos) OR (func^.size IN {1,2,4,8}) THEN
      StackTop( - func^.size )
    ELSE
      err(200)
    END;
  END SpaceForFunction;
  PROCEDURE PrepCall(VAR x: Item; VAR fp: ParPtr; VAR regs: LONGINT);
    VAR func: StrPtr; Rn: Register;
  BEGIN
    Rn := 0;
    WITH x DO
      IF (mode = procMd) OR (mode = codMd) THEN
        func := proc^.typ; fp := proc^.firstParam;
      ELSIF typ^.form = ProcTyp THEN
        func := typ^.resTyp; fp := typ^.firstPar;
        LoadP(x);                 (* load procedure variable *)
        Rn := R; ReleaseReg(Rn);  (* inhibit save of register Rn *)
      ELSE
        func := notyp; fp := NIL;
        err(136);  (* call of an object which is not a procedure *)
      END;
      SaveRegs(regs);
      IF Rn # 0 THEN SetbusyReg(Rn) END;  (* re-reserve register Rn *)
      IF func # notyp THEN SpaceForFunction(func) END;
    END (*WITH*);
  END PrepCall;
  PROCEDURE GenParam(VAR ap: Item; f: ParPtr);
    VAR fp: Item;
  BEGIN
    SetstkMd(fp, f^.typ);
    IF f^.varpar THEN
      IF (fp.typ^.form = Array) & fp.typ^.dyn & (fp.typ^.ElemTyp = bytetyp) THEN
        DynArray(fp, ap);
      ELSIF (fp.typ^.form = Array) & fp.typ^.dyn &
            (ap.typ^.form = Array) & (ap.typ^.ElemTyp = fp.typ^.ElemTyp) THEN
        DynArray(fp, ap);
      ELSIF (ap.typ = fp.typ) OR
        (fp.typ = wordtyp) & (ap.typ^.size = 2) OR
        (fp.typ = bytetyp) & (ap.typ^.size = 1) OR
        (fp.typ = addrtyp) & (ap.typ^.form = Pointer) THEN
        IF (ap.mode = procMd) & (f^.typ^.form # ProcTyp) THEN
          err(137)
        ELSE
          MoveAdr(ap, fp)
        END;
      ELSE
        err(137);  (* type of VAR par is not identical to that of actual par *)
      END;
    ELSE
      GenAssign(fp, ap);  (* type check in GenAssign *)
    END;
    Release(ap);
  END GenParam;
  PROCEDURE RestoreResultAndRegs(VAR x : Item; regs : LONGINT);
    VAR y, z : Item; sz : INTEGER;
  BEGIN
    WITH x DO
      SetstkMd(x, typ);   (* result on top of stack *)
      IF regs # 0D THEN  (* saved registers above result *)
        (* Caution: saved registers remain busy, so the LoadD(x) *)
        (* -------  below gets a pool-register which is NOT in   *)
        (*          the set of the registers to be restored.     *)
        IF SimpleT(x) THEN LoadD(x)
        ELSIF RealT(x) THEN LoadF(x)
        ELSE (* structured type *)
          sz := typ^.size;
          IF NOT(sz IN {1,2,4,8}) THEN
            err(200); (* function result size not implemented! *)
          ELSE
            IF sz IN {1,2,4} THEN (* byte/word/long result *)
              SetstkMd(z, typ);
              SetregMd(y, D0, typ); Move(z,y);
              RestoreRegs(regs); regs := 0D;
              Move(y,z);
            ELSE (* double-longword result *)
              SetstkMd(z, dbltyp);
              SetregMd(y, D0, dbltyp); Move(z,y);
              SetregMd(y, D1, dbltyp); Move(z,y);
              RestoreRegs(regs); regs := 0D;
              SetregMd(y, D1, dbltyp); Move(y,z);
              SetregMd(y, D0, dbltyp); Move(y,z);
            END;
          END;
        END;
        RestoreRegs(regs);
      END (*regs*);
    END (*WITH*);
  END RestoreResultAndRegs;
  PROCEDURE GenCall(VAR x: Item; regs: LONGINT);
    VAR pd: PDPtr; y, z: Item;
  BEGIN
    WITH x DO
      IF (mode = procMd) THEN
        pd := proc^.pd;
        IF pd^.adr # 0 THEN (* module internal call *)
          IF pd^.lev > 0 THEN SetupSL(pd^.lev) END;
          CallInt(proc);
        ELSE (* external call *)
          CallExt(proc);
        END;
        typ := proc^.typ;
      ELSIF (mode = codMd) THEN
        Put16(proc^.cnum); typ := proc^.typ;
      ELSIF (mode <= DregMd) & (typ # undftyp) & (typ^.form = ProcTyp) THEN
        CallInd(x); typ := typ^.resTyp;
      END;
      IF typ # notyp THEN (* function call *)
        RestoreResultAndRegs(x,regs)
      ELSE (* procedure call *)
        RestoreRegs(regs)
      END;
    END (*WITH*);
  END GenCall;
  PROCEDURE GenEnter(VAR l: INTEGER; lev: INTEGER);
  BEGIN
    Link(l, lev); sp := 0; sp0 := 0;
  END GenEnter;
  PROCEDURE GenResult(VAR x: Item; proc: ObjPtr; VAR l: INTEGER);
    VAR res: Item; resadr : INTEGER;
  BEGIN
    IF x.typ # notyp THEN (* function *)
      IF proc^.pd^.lev > 0 THEN
        resadr := LocParStartAdr + proc^.pd^.size
      ELSE
        resadr := GlbParStartAdr + proc^.pd^.size
      END;
      SetlocMd(res, resadr, proc^.typ);
      GenAssign(res, x);
    END;
    StackTop(sp - sp0);
    GenFJ(l);
  END GenResult;
  PROCEDURE GenReturn(proc: ObjPtr; l: INTEGER);
  BEGIN
    IF proc^.class = Module THEN
      IF l # 0 THEN FixLink(l) END;
    ELSE  (* Proc *)
      IF proc^.typ # notyp THEN GenHalt(2) END; (* function *)
      IF l # 0 THEN FixLink(l) END;
      Unlink(proc^.pd^.size, proc^.pd^.lev);
    END;
  END GenReturn;
  PROCEDURE GenCase1(VAR x: Item; VAR l0: INTEGER);
  BEGIN
    SRTest(x);
    IF (x.typ^.form < Bool) OR ((x.typ^.form > Enum) & (x.typ^.form # Double)) THEN
      err(140) (* illegal type of case expression *)
    END;
    LoadX(x, long); ReleaseReg(x.R); l0 := 0; GenFJ(l0); sp := sp + 4;
  END GenCase1;
  PROCEDURE GenCase2;
  BEGIN
    ExitCase;
  END GenCase2;
  PROCEDURE GenCase3(VAR x: Item; l0, l1, n: INTEGER;
                     VAR tab: ARRAY OF LabelRange);
    VAR i: INTEGER; base, j: INTEGER;
  BEGIN
    base := pc + 2; Put16(l1 - base); (* ELSE entry *)
    IF n > 0 THEN (* if NOT empty CASE statement *)
      i := 0; j := tab[0].low;
      WHILE i < n DO
        WHILE j < tab[i].low DO
          Put16(l1 - base); INC(j); (* ELSE entry *)
        END;
        FOR j := j TO tab[i].high DO
          Put16(tab[i].label - base);
        END;
        INC(i);
      END;
      fixup(l0); EnterCase(x, base, tab[0].low, tab[n-1].high);
    ELSE
      fixup(l0); EnterCase(x, l1, 1, 0); (* if empty CASE statement *)
    END;
    sp := sp - 4;
  END GenCase3;
  PROCEDURE GenFor1(v: Item; VAR e1: Item);
  BEGIN
    SRTest(v);
    IF (v.typ^.form < Bool) OR ((v.typ^.form > Enum) & (v.typ^.form # Double)) THEN
      err(142); (* illegal type of control variable *)
    END;
  END GenFor1;
  PROCEDURE GenFor2(v: Item; VAR e1, e2: Item);
    VAR w: Item;
  BEGIN
    w := v; SRTest(w); (* don't change v! *)
    SRTest(e1); SRTest(e2);
    IF e2.mode # conMd THEN LoadD(e2) END;
    IF w.typ = dbltyp THEN
      IF (e1.typ = inttyp) & (e1.mode = conMd) THEN SetconMd(e1,LongVal(e1),dbltyp) END;
      IF (e2.typ = inttyp) & (e2.mode = conMd) THEN SetconMd(e2,LongVal(e2),dbltyp) END;
    END;
    (* starting and limiting value must be compatible *)
    (* with the type of the control variable !        *)
    (* this rule is broken for constants. HS 31.3.91. *)
    IF w.typ = e1.typ THEN GenAssign(v, e1)
    ELSE err(133) (* incompatible assignment *)
    END;
    IF w.typ = e2.typ THEN
      IF e2.mode # conMd THEN
        SetstkMd(w, e2.typ); GenAssign(w, e2);
        e2 := w; e2.mode := RindMd; (* transform to 'RindMd' *)
        sp := sp + e2.typ^.size;
      END;
    ELSE err(117) (* incompatible limit *)
    END;
    Release(e2);
  END GenFor2;
  PROCEDURE GenFor3(v: Item; VAR e2, e3: Item; VAR l0, l1: INTEGER);
    VAR f: StrForm; c: Condition; step: LONGINT;
  BEGIN
    SRTest(v); f := v.typ^.form;
    l0 := pc; Cmp2(v, e2); Release(v);
    (* step must be a constant of type INTEGER/LONGINT. *)
    SRTest(e3);
    IF e3.typ # inttyp THEN
      IF (f = Double) & (e3.typ = dbltyp) THEN
      ELSE err(117) END; (* illegal type for step *)
    END;
    step := LongVal(e3);
    IF f = Double THEN SetconMd(e3, step, dbltyp) END;
    IF ((f = Bool) OR (f = Char) OR (f = Enum)) & (ABS(step) # 1) THEN
      err(138) (* illegal value for step *)
    END;
    IF step > 0 THEN
      IF (f = Int) OR (f = Double) THEN c := GT ELSE c := HI END;
    ELSIF step < 0 THEN
      IF (f = Int) OR (f = Double) THEN c := LT ELSE c := CS END;
    ELSE
      err(141) (* step must not be 0 *)
    END;
    l1 := 0; Jf(c, l1);
  END GenFor3;
  PROCEDURE GenFor4(v: Item; VAR e2, e3: Item; l0, l1: INTEGER);
    VAR c: Condition; f: StrForm; chk: BOOLEAN;
  BEGIN
    SRTest(v); f := v.typ^.form;
    chk := ovflchk; ovflchk := FALSE; Add2(v, e3); ovflchk := chk; Release(v);
    IF (f = Int) OR (f = Double) THEN
      c := VC;
    ELSIF LongVal(e3) > 0 THEN
      c := CC;
    ELSE
      c := CS;
    END;
    Jb(c, l0); fixup(l1);
    IF e2.mode # conMd THEN
      StackTop(e2.typ^.size); IF sp >= e2.typ^.size THEN sp := sp - e2.typ^.size END;
    END;
  END GenFor4;
  PROCEDURE GenLoop1(VAR s, m: INTEGER; n: INTEGER);
  BEGIN
    s := sp0; sp0 := sp; m := n;
  END GenLoop1;
  PROCEDURE GenLoop2(s, m: INTEGER; VAR n: INTEGER; VAR tab: ExitTable);
  BEGIN
    WHILE n > m DO fixup(tab[n-1]); n := n - 1 END;
    sp0 := s;
  END GenLoop2;
  PROCEDURE GenExit(VAR n: INTEGER; VAR tab: ExitTable);
  BEGIN
    StackTop(sp - sp0);
    IF n <= MaxExit THEN
      tab[n] := 0; GenFJ(tab[n]); INC(n);
    ELSE
      err(93);  (* too many exit statements *)
    END;
  END GenExit;
  PROCEDURE GenEnterMod(modList: ObjPtr; mno, pno: INTEGER);
    VAR obj: ObjPtr; i: INTEGER;
  BEGIN
    EnterModule;
    maxP := pno + 1;  (* 1 for initialization *)
    maxM := mno + 1;  (* 1 for System *)
    sp := 0; sp0 := 0;
    FOR i := 2 TO maxM DO InitModule(i-1) END;
  END GenEnterMod;
  PROCEDURE GenExitMod;
  BEGIN
    ExitModule;
  END GenExitMod;
END M2CA. (* Copyright Departement Informatik, ETH Zuerich, Switzerland, 1992 *)
