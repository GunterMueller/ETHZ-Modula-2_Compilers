IMPLEMENTATION MODULE M2EM; (* Hermann Seiler 19.4.85 / 10.6.86 / 30.5.90 *)
  FROM SYSTEM IMPORT
          WORD, ADR, LONG, SHORT, SHIFT, VAL;
  FROM M2DM IMPORT
          ObjPtr, StrPtr, ParPtr, PDPtr, KeyPtr,
          ObjClass, StrForm, Standard, ConstValue, PDesc,
          Object, Structure, rngchk,
          notyp, undftyp, booltyp, chartyp, cardtyp, cardinttyp,
          inttyp, bitstyp, lcardtyp, dbltyp, realtyp, lrltyp,
          proctyp, stringtyp, addrtyp, wordtyp, bytetyp,
          WordSize, MaxChar, MaxCard, MinInt, MaxInt, MinDouble, MaxDouble;
  FROM M2SM IMPORT
          Symbol, Mark;
  FROM M2HM IMPORT
          D0, D1, SB, MP, SP,
          byte, word, long,
          Condition, RegType, Register,
          WidType, ItemMode, ItSet, Item, curLev,
          LongVal, WordVal, SimpleC, SignedT, SimpleT, RealT,
          GetReg, Release, ReleaseReg, LockReg, UnlockReg, SetbusyReg,
          Isz, SetregMd, SetconMd, SetglbMd, SetstkMd,
          InvertCC, Jf, StackTop, GenHalt,
          LoadAdr, LoadD, LoadP, LoadX, Move, MoveAdr,
          Neg1, Abs1, Cap1, Tst1, Com1, Inc1, Dec1,
          Add2, Sub2, And2, Or2, Eor2, Div2, Mod2,
          Mul2, Cmp2, In2, ShiType, Shi2, Ash2,
          ConvertTyp, ConIndex, VarIndex, GetHigh, Normalize,
          CheckHigh, CheckClimit, CheckRange,
          CheckDbltoSingle, CheckPointer, PreLoad,
          FMove, LoadF, FMonad, FDyad;
  FROM M2LM IMPORT
          PutWord, maxP, maxM,
          FixLink, fixup, MergedLinks;
  VAR
          mask   :  ARRAY [ 0 .. 32 ] OF LONGINT;
          wtab   :  ARRAY [ 0..wtabmax ] OF
                      RECORD
                        witem, mitem : Item;
                        locked : BOOLEAN
                      END;
  PROCEDURE err(n : CARDINAL);
  BEGIN
     Mark(n);
  END err;
  PROCEDURE Put16(w : WORD);
  BEGIN
    PutWord(w);
  END Put16;
  PROCEDURE IncAdr(VAR adr : INTEGER; s : INTEGER);
  BEGIN
    IF (adr >= 0) & (s <= MaxInt - adr) OR
       (adr <  0) & (s >= MinInt - adr) THEN adr := adr + s
    ELSE err(211) (* address underflow/overflow *)
    END;
  END IncAdr;
  PROCEDURE AllocVar(obj : ObjPtr; VAR adr : INTEGER);
    VAR s : INTEGER;
  BEGIN
    (* obj^.class = Var *)
    WITH obj^ DO
      (* allocate always an even number of bytes :   *)
      (* so adr should never be set to an odd value. *)
      s := typ^.size; IF ODD(s) THEN INC(s) END;
      (* negative allocation for global and local variables *)
      IncAdr(adr, -s); vadr := adr;
    END (*WITH*);
  END AllocVar;
  PROCEDURE AllocPar(par : ParPtr; VAR adr : INTEGER);
    CONST PointerSize = 4;
    VAR   s : INTEGER;
  BEGIN
    WITH par^ DO
      s := typ^.size;
      (* always WORD-alignment for parameters on stack : *)
      IF ODD(s) THEN INC(s) END;
      IF (typ^.form = Array) & typ^.dyn THEN
        (* s = size of formal type for dynamic array parameter *)
        IncAdr(adr, -s)
      ELSIF varpar THEN
        IncAdr(adr, -PointerSize)
      ELSE
        IncAdr(adr, -s)
      END;
    END (*WITH*);
  END AllocPar;
  PROCEDURE AllocFld(obj : ObjPtr; VAR adr : INTEGER);
    CONST ByteSize = 1;
    VAR   s : INTEGER;
  BEGIN
    (* obj^.class = Field *)
    WITH obj^ DO
      s := typ^.size;
      IF NOT((typ^.form <= Opaque) & (s = ByteSize)) THEN
        (* WORD-alignment for structured types and *)
        (* types with a size > ByteSize.           *)
        IF ODD(adr) THEN INC(adr) END;
      END;
      offset := adr;
      IncAdr(adr, s)
    END (*WITH*);
  END AllocFld;
  PROCEDURE SRTest(VAR x : Item);
  BEGIN
    WITH x DO
      IF typ^.form = Range THEN typ := typ^.RBaseTyp END;
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
  PROCEDURE SetBaseLimits(VAR x : Item; VAR lo, hi : INTEGER);
    VAR sz : WidType; mi, ma : INTEGER;
  BEGIN
    (* x.typ^.form = Set *)
    Isz(x,sz); (* take width of set before type is changed *)
    WITH x DO
      typ := typ^.SBaseTyp;
      IF typ^.form = Enum THEN
        mi := 0; ma := typ^.NofConst - 1;
      ELSIF typ^.form = Range THEN
        mi := typ^.min; ma := typ^.max;
        typ := typ^.RBaseTyp;
      ELSE
        mi := 0; ma := SHIFT(8, sz) - 1;
      END;
    END (*WITH*);
    lo := mi;
    hi := ma;
  END SetBaseLimits;
  PROCEDURE ConnectToWith(VAR x : Item; flev : CARDINAL);
  BEGIN
    IF (flev > 0) & (flev <= wtabmax) & (flev <= wlev) THEN
      (* caution : typ of item is changed. *)
      x := wtab[flev].witem;
    ELSE
      Release(x);
      SetglbMd(x, 0, undftyp);
    END;
  END ConnectToWith;
  PROCEDURE GenItem(VAR x : Item; y, scope : ObjPtr);
  BEGIN
    IF y <> NIL THEN
      WITH x DO
        typ := y^.typ;
        CASE y^.class OF
          Const :    mode  := conMd;    val := y^.conval;
        | Typ :      mode  := typMd;
        | Var :      indir := y^.varpar;
                     mod   := y^.vmod;  lev := y^.vlev;
                     adr   := y^.vadr;  off := 0;
                     IF mod = 0 THEN
                       IF lev = 0 THEN (* global *)
                         mode := RindMd; R := SB + 8;
                       ELSE (* local *)
                         mode := RindMd; R := MP + 8;
                       END;
                     ELSE (* external *)
                       mode := RindMd; R := SB + 8; indir := TRUE;
                       off  := adr;  adr := (maxP + mod)*4;
                     END;
                     (* dynamic arrays always descriptor indirect : *)
                     IF (typ^.form = Array) & typ^.dyn THEN indir := TRUE END;
        | Field :    ConnectToWith(x, scope^.name); typ := y^.typ;
                     IF mode < conMd THEN
                       (* reference to indir, adr, off allowed. *)
                       IF indir THEN off := off + y^.offset
                       ELSE adr := adr + y^.offset END;
                     END;
        | Proc :     mode := procMd; proc := y;
        | Code :     mode := codMd;  proc := y;
        | Module :   SetglbMd(x, 0, typ); err(107);
        | Temp :     SetglbMd(x, 0, undftyp); err(50);
        END (*CASE*);
      END (*WITH*);
    ELSE
      SetglbMd(x, 0, undftyp);
      err(50);
    END;
  END GenItem;
  PROCEDURE GenIndex(VAR x, y : Item);
    VAR i, up, low, elsize : INTEGER;
        inxt, elet : StrPtr;
        z : Item;
  BEGIN
    SRTest(y);
    IF x.typ^.form = Array THEN
      elet := x.typ^.ElemTyp;
      elsize := elet^.size;
      IF x.typ^.dyn THEN
        (* dynamic array always descriptor indirect : *)
        IF (y.typ = inttyp) OR (y.typ = cardtyp) OR
           (y.typ = cardinttyp) OR (y.typ = dbltyp) THEN
          z := x; GetHigh(z); (* inhibit change of x *)
          (* the minimal width of an index must be word! *)
          IF (y.typ^.size <= 2) THEN LoadX(y,word); y.typ := inttyp
          ELSE LoadD(y) END;
          CheckHigh(y,z);
          VarIndex(x,y,elsize);
        ELSE
          err(109); Release(y);
        END;
      ELSE (* not dyn *)
        up := 0; low := 0;
        WITH x.typ^.IndexTyp^ DO
          inxt := RBaseTyp;
          IF form = Range THEN up := max; low := min END;
        END (*WITH*);
        IF SimpleC(y) THEN
          (* constant index : *)
          i := WordVal(y);
          IF inxt <> y.typ THEN
            IF (i < 0) OR ((inxt = cardtyp) & (y.typ <> inttyp))
            OR ((inxt = inttyp) & (y.typ <> cardtyp)) THEN
              err(109);
            END;
          END;
          IF ((low <= i) &  (i <= up)) &
             ((low >= 0) OR (i <= (MaxInt + low))) THEN
            i := i - low; (* normalize index to 0 *)
          ELSE
            err(108); i := 0;
          END;
          (* now i >= 0 ! : *)
          IF (elsize = 0) OR (i <= MaxInt DIV elsize) THEN
            i := elsize * i;
          ELSE
            err(108); i := 0;
          END;
          ConIndex(x,i);
        ELSE
          (* variable index : *)
          IF inxt <> y.typ THEN
            IF ((inxt <> cardtyp) OR (y.typ <> inttyp)) &
               ((inxt <> inttyp)  OR (y.typ <> cardtyp)) &
               (y.typ <> dbltyp) & (y.typ <> cardinttyp) THEN
              err(109);
            END;
          END;
          (* the minimal width of an index must be word! *)
          IF (y.typ^.size <= 2) THEN LoadX(y,word); y.typ := inttyp
          ELSE LoadD(y); y.typ := dbltyp END;
          Normalize(y,low);
          IF (low >= 0) OR (up <= (low + MaxInt)) THEN
            i := up - low;
          ELSE
            err(108); i := 0;
          END;
          CheckClimit(y,i);
          VarIndex(x,y,elsize);
        END (*variable index*);
      END (*not dyn*);
      x.typ := elet;
    ELSE (*form <> Array*)
      err(109);
      Release(y);
    END;
  END GenIndex;
  PROCEDURE GenField(VAR x : Item; f : ObjPtr);
  BEGIN
    WITH x DO
      (* typ^.form = Record *)
      IF (f <> NIL) & (f^.class = Field) THEN
        ConIndex(x, f^.offset);
        typ := f^.typ;
      ELSE
        err(110); Release(x);
        SetglbMd(x, 0, undftyp);
      END;
    END (*WITH*);
  END GenField;
  PROCEDURE GenDeRef(VAR x : Item);
  BEGIN
    WITH x DO
      IF (typ^.form = Pointer) OR (typ = addrtyp) THEN
        CheckPointer(x);
        IF (mode < conMd) & NOT(indir) THEN
          indir := TRUE;  off := 0;
        ELSIF mode <> conMd THEN
          LoadP(x); mode := RindMd; (* transform to 'RindMd' *)
        ELSE
          err(111); (* illegal dereferencing *)
        END;
        IF typ = addrtyp THEN typ := bytetyp
        ELSE typ := typ^.PBaseTyp END;
      ELSE
        err(111); (* illegal dereferencing *)
      END;
    END (*WITH*);
  END GenDeRef;
  PROCEDURE GenNeg(VAR x : Item);
    VAR f : StrForm; lv : LONGINT;
  BEGIN SRTest(x);
    WITH x DO
      f := typ^.form;
      IF SimpleC(x) OR ((mode = conMd) & RealT(x)) THEN
        lv := LongVal(x);
        IF (f = Int) OR ((f = Card) & (lv <= 32767D)) THEN
          IF WordVal(x) > MIN(INTEGER) THEN
            SetconMd(x, -lv, inttyp);
          ELSE
            err(201);
          END;
        ELSIF f = Double THEN
          IF lv > MIN(LONGINT) THEN
            SetconMd(x, -lv, dbltyp)
          ELSE
            err(201);
          END;
        ELSIF f = Real THEN
          val.R := - val.R;
          SetconMd(x, LongVal(x), realtyp)
        ELSIF f = LongReal THEN
          val.X := - val.X;
        ELSE err(112);
        END;
      ELSE (* x not a constant *)
        IF (f = Int) OR (f = Double) THEN Neg1(x)
        ELSIF (f = CardInt) THEN Neg1(x); typ := inttyp
        ELSIF (f = Real) OR (f = LongReal) THEN FMonad(NonStand,x)
        ELSE err(112);
        END;
      END;
    END (*WITH*);
  END GenNeg;
  PROCEDURE GenNot(VAR x : Item);
    VAR t : CARDINAL;
  BEGIN SRTest(x);
    WITH x DO
      IF typ^.form = Bool THEN
        IF mode = conMd THEN
          val.B := NOT(val.B);
          SetconMd(x, ORD(val.B), typ);
        ELSIF mode = cocMd THEN
          CC := InvertCC(CC);
          t := Tjmp; Tjmp := Fjmp; Fjmp := t;
        ELSE
          Tst1(x);
          setCC(x,NE);
        END;
      ELSE
        err(113);
      END;
    END (*WITH*);
  END GenNot;
  PROCEDURE GenAnd(VAR x : Item);
  BEGIN SRTest(x);
    WITH x DO
      IF mode = cocMd THEN
        Jf(CC, Fjmp);
        FixLink(Tjmp);
      ELSIF (typ^.form = Bool) & (mode <> conMd) THEN
        Tst1(x);
        setCC(x,EQ);
        Jf(CC, Fjmp);
        FixLink(Tjmp);
      ELSIF typ^.form <> Bool THEN
        err(122); Release(x);
        SetconMd(x, 0D, booltyp);
      END;
    END (*WITH*);
  END GenAnd;
  PROCEDURE GenOr(VAR x : Item);
  BEGIN SRTest(x);
    WITH x DO
      IF mode = cocMd THEN
        Jf(InvertCC(CC), Tjmp);
        FixLink(Fjmp);
      ELSIF (typ^.form = Bool) & (mode <> conMd) THEN
        Tst1(x);
        setCC(x,NE);
        Jf(CC, Tjmp);
        FixLink(Fjmp);
      ELSIF typ^.form <> Bool THEN
        err(125); Release(x);
        SetconMd(x, 1D, booltyp);
      END;
    END (*WITH*);
  END GenOr;
  PROCEDURE GenSingSet(VAR x, e : Item);
    VAR s : StrPtr; y : Item; Dn : Register;
        v, lo, hi : INTEGER;
  BEGIN (* x.typ^.form = Set *)
    SRTest(e);
    s := x.typ; (* hold original type of set *)
    SetBaseLimits(x,lo,hi);
    IF (e.typ = x.typ) OR
       (((e.typ=inttyp) OR (e.typ=cardinttyp)) & (s = bitstyp)) THEN
      IF SimpleC(e) THEN (* e is constant *)
        v := WordVal(e);
        IF (v >= lo) & (v <= hi) & (hi <= 31) THEN
          SetconMd(x, SHIFT(1D, v), s)
        ELSE
          SetconMd(x, 0D, s);
          err(202);
        END
      ELSE (* e is expression *)
        GetReg(Dn,Dreg);
        SetregMd(x, Dn, s);
        SetconMd(y, 1D, s);
        Move(y,x);
        LoadX(e,word);
        e.typ := inttyp;
        CheckRange(e,lo,hi,0);
        Shi2(x,e,Lsl);
      END
    ELSE
      err(116);
      SetregMd(x, D0, s);
    END;
    Release(e);
  END GenSingSet;
  PROCEDURE GenSet(VAR x, e1, e2 : Item);
    VAR s : StrPtr; y : Item;
        Dn, Dy : Register;
        lo, hi, v1, v2 : INTEGER; lv : LONGINT;
  BEGIN (* x.typ^.form = Set *)
    SRTest(e1); SRTest(e2);
    s := x.typ; (* hold original type of set *)
    SetBaseLimits(x,lo,hi);
    IF (e1.typ = x.typ) & (e2.typ = x.typ) OR
       ( ((e1.typ = inttyp) OR (e1.typ = cardinttyp)) &
         ((e2.typ = inttyp) OR (e2.typ = cardinttyp)) &
         (s = bitstyp) ) THEN
      IF SimpleC(e1) & SimpleC(e2) THEN
        (* constant set-constructor : *)
        v1 := WordVal(e1);
        v2 := WordVal(e2);
        IF ((lo <= v2) & (v2 <= hi)) & (v1 <= v2) & (hi <= 31) THEN
          lv := mask[ v2 + 1 - v1 ];
          SetconMd(x, SHIFT(lv, v1), s);
        ELSE
          SetconMd(x, 0D, s);
          err(202);
        END
      ELSE
        (* variable set-constructor : *)
        GetReg(Dn,Dreg);
        SetregMd(x, Dn, dbltyp); (* dbltyp gives long operation *)
        SetconMd(y, 080000000H, dbltyp);
        Move(y,x); (* set sign bit *)
        LoadX(e2,word); e2.typ := inttyp;
        CheckRange(e2,lo,hi,0);
        GetReg(Dy,Dreg);
        SetregMd(y, Dy, e2.typ);
        Move(e2,y); Inc1(y);
        LoadX(e1,word); e1.typ := inttyp;
        Sub2(e2,e1);
        CheckClimit(e2,hi-lo);
        Shi2(x,e2,Asr); Shi2(x,y,Rol);
        Release(y);
        x.typ := s;   (* restore original type of set *)
      END
    ELSE
      err(116);
      SetregMd(x, D0, s);
    END;
    Release(e1);
    Release(e2);
  END GenSet;
  PROCEDURE GenIn(VAR x, y : Item);
    VAR f : StrForm; s : StrPtr;
        v, lo, hi : INTEGER; b : BOOLEAN;
  BEGIN
    SRTest(x);
    f := x.typ^.form;
    s := y.typ; (* hold original type of set *)
    IF ((Bool <= f) & (f <= Enum)) & (y.typ^.form = Set) THEN
      SetBaseLimits(y,lo,hi);
      IF (x.typ = y.typ) OR (x.typ = inttyp) & (s = bitstyp)
                         OR (x.typ = cardinttyp) & (s = bitstyp) THEN
        y.typ := s; (* recover type of set *)
        IF SimpleC(x) THEN (* constant element x *)
          v := WordVal(x);
          IF (v >= lo) & (v <= hi) & (hi <= 31) THEN
            IF y.mode = conMd THEN (* constant set y *)
              b := v IN y.val.S;
              SetconMd(x, ORD(b), booltyp);
            ELSE (* variable set y *)
              LoadD(y);
              In2(x,y);
              setCC(x,EQ);
            END;
          ELSE
            SetconMd(x, 0D, booltyp);
          END;
        ELSE (* variable element x *)
          LoadD(y); (* load y first, should both x and y have stkMd *)
          LoadD(x);
          In2(x,y);
          setCC(x,EQ);
        END;
      ELSE
        Release(x);
        SetregMd(x, D0, booltyp);
        err(114);
      END;
    ELSE
      Release(x);
      SetregMd(x, D0, booltyp);
      err(115);
    END;
    x.typ := booltyp;
    Release(y);
  END GenIn;
  PROCEDURE GenWith(VAR x : Item; VAR fadr : INTEGER);
    VAR ob : Object; obj : ObjPtr; xt : StrPtr;
  BEGIN
    INC(wlev);
    IF wlev > wtabmax THEN
      err(236); Release(x);
      RETURN;
    END;
    xt := x.typ; (* holds original type of record *)
    WITH wtab[wlev] DO
      IF wlev <= 2 THEN
        LoadAdr(x); x.mode := RindMd; (* transform to 'RindMd' *)
        LockReg(x.R);
        locked := TRUE;
      ELSE
        (* allocate anonymous variable of type ADDRESS. *)
        obj := ADR(ob);
        WITH obj^ DO
          class := Var; typ := addrtyp;
          varpar := FALSE; vadr := fadr;
          vmod := 0; vlev := curLev;
        END (*WITH*);
        AllocVar(obj, fadr);
        GenItem(mitem, obj, NIL);
        MoveAdr(x,mitem);
        Release(x);
        locked := FALSE;
        x := mitem;
        (* reference is indirect thru mitem : *)
        IF x.mode < conMd THEN x.indir := TRUE END;
      END;
      x.typ := xt;
      witem := x;
    END (*WITH wtab*);
  END GenWith;
  PROCEDURE GenWith2;
  BEGIN
    IF wlev > 0 THEN
      IF wlev <= wtabmax THEN
        WITH wtab[wlev] DO
          IF locked THEN
            UnlockReg(witem.R);
            ReleaseReg(witem.R);
            locked := FALSE;
          ELSE
            Release(witem);
          END;
        END (*WITH wtab*);
      END;
      DEC(wlev);
    END;
  END GenWith2;
  PROCEDURE InitM2EM;
    VAR k : CARDINAL; exp : LONGINT;
  BEGIN
    wlev := 0;
    exp := 0D; mask[0] := 0D; mask[32] := -1D;
    FOR k := 1 TO 31 DO exp := exp + exp + 1D; mask[k] := exp END;
  END InitM2EM;
  PROCEDURE GenOp(op : Symbol; VAR x, y : Item);
    VAR f, g : StrForm; c : Condition;
        xval, yval : ConstValue; xx : Item;
  BEGIN
    SRTest(x); f := x.typ^.form;
    SRTest(y); g := y.typ^.form;
    IF x.typ <> y.typ THEN
      IF ((f = Int) OR (f = CardInt)) & (g = Card) & (y.mode = conMd)
       & (y.val.C <= MaxInt) THEN y.typ := x.typ
      ELSIF (f = Card) & ((g = Int) OR (g = CardInt)) & (x.mode = conMd)
       & (x.val.C <= MaxInt) THEN x.typ := y.typ; f := Int
      ELSIF (f = Double) & (g = LCard) & (x.mode = conMd) THEN
        x.typ := y.typ; f := LCard
      ELSIF (f = LCard) & (g = Double) & (y.mode = conMd) THEN
        y.typ := x.typ
      ELSIF (g = CardInt) & ((f = Int) OR (f = Card)) THEN
        g := f; y.typ := x.typ
      ELSIF (f = CardInt) & ((g = Int) OR (g = Card)) THEN
        f := g; x.typ := y.typ
      ELSIF (x.typ = addrtyp) & (g = Pointer) THEN f := Pointer
      ELSIF ((f <> Pointer) OR (y.typ <> addrtyp)) &
            ((f <> Double) OR (g <> Double)) THEN err(117);
      END;
    END;
    IF (x.mode = conMd) & (y.mode = conMd) THEN
      xval := x.val; yval := y.val;
      CASE op OF
        times : IF f = Card THEN
                  IF (xval.C = 0) OR (yval.C <= MaxCard DIV xval.C) THEN
                    xval.C := xval.C * yval.C;
                  ELSE err(203)
                  END
                ELSIF f = Int THEN
                  IF (xval.I = 0) OR
                  ((y.val.I <> MIN(INTEGER)) & (x.val.I <> MIN(INTEGER)) &
                   (ABS(yval.I) <= MaxInt DIV ABS(xval.I))) THEN
                    xval.I := xval.I * yval.I;
                  ELSE err(203)
                  END
                ELSIF f = Double THEN
                  IF (xval.D = 0D) OR
                  ((y.val.D <> MIN(LONGINT)) & (x.val.D <> MIN(LONGINT)) &
                   (ABS(yval.D) <= MaxDouble DIV ABS(xval.D))) THEN
                    xval.D := xval.D * yval.D;
                  ELSE err(203)
                  END
                ELSIF f = Real THEN
                  IF (xval.R = 0.0) OR (ABS(xval.R) <= FLOAT(1)) OR
                     (ABS(yval.R) <= MAX(REAL) / ABS(xval.R)) THEN
                    xval.R := xval.R * yval.R;
                  ELSE err(203)
                  END
                ELSIF f = LongReal THEN
                  IF (xval.X = 0.0D) OR (ABS(xval.X) <= FLOATD(1)) OR
                    (ABS(yval.X) <= MAX(LONGREAL) / ABS(xval.X)) THEN
                    xval.X := xval.X * yval.X;
                  ELSE err(203)
                  END
                ELSIF f = Set THEN
                  xval.S  := xval.S  * yval.S;
                ELSE err(118)
                END;
      | slash : IF f = Real THEN
                  IF (ABS(yval.R) >= FLOAT(1)) OR ((yval.R <> 0.0) &
                     (ABS(xval.R) <= ABS(yval.R) * MAX(REAL))) THEN
                    xval.R := xval.R / yval.R;
                  ELSE err(204)
                  END
                ELSIF f = LongReal THEN
                  IF (ABS(yval.X) >= FLOATD(1)) OR ((yval.X <> 0.0D) &
                   (ABS(xval.X) <= ABS(yval.X) * MAX(LONGREAL))) THEN
                    xval.X := xval.X / yval.X;
                  ELSE err(204)
                  END
                ELSIF f = Set THEN
                  xval.S  := xval.S / yval.S;
                ELSE err(119)
                END;
      | div :   IF f = Card THEN
                  IF yval.C > 0 THEN
                    xval.C := xval.C DIV yval.C;
                  ELSE err(205)
                  END
                ELSIF f = Int THEN
                  IF yval.I <> 0 THEN
                    xval.I := xval.I DIV yval.I;
                  ELSE err(205)
                  END
                ELSIF f = Double THEN
                  IF yval.D <> 0D THEN
                    xval.D := xval.D DIV yval.D;
                  ELSE err(205)
                  END
                ELSE err(120)
                END;
      | rem :   IF (f = Int) OR (f = Card) OR (f = Double) THEN
                  err(200)
                ELSE err(121)
                END;
      | mod :   IF f = Card THEN
                  IF yval.C > 0 THEN
                    xval.C := xval.C MOD yval.C;
                  ELSE err(205)
                  END
                ELSIF f = Int THEN
                  IF (xval.I >= 0) & (yval.I > 0) THEN
                    xval.I := xval.I MOD yval.I;
                  ELSE err(205)
                  END
                ELSIF f = Double THEN
                  IF (xval.D >= 0D) & (yval.D > 0D) THEN
                    xval.D := xval.D MOD yval.D;
                  ELSE err(205)
                  END
                ELSE err(121)
                END;
      | and :   IF f = Bool THEN xval.B := xval.B AND yval.B
                ELSE err(122)
                END;
      | plus :  IF f = Card THEN
                  IF yval.C <= MaxCard - xval.C THEN
                    xval.C := xval.C + yval.C;
                  ELSE err(206)
                  END
                ELSIF f = Int THEN
                  IF (xval.I >= 0) & (yval.I <= MaxInt - xval.I) OR
                     (xval.I <  0) & (yval.I >= MIN(INTEGER) - xval.I) THEN
                    xval.I := xval.I + yval.I;
                  ELSE err(206)
                  END
                ELSIF f = Real THEN
                  IF (xval.R >= 0.0) & (yval.R <= MAX(REAL) - xval.R) OR
                     (xval.R <  0.0) & (yval.R >= MIN(REAL) - xval.R) THEN
                    xval.R := xval.R + yval.R;
                  ELSE err(206)
                  END
                ELSIF f = LongReal THEN
                  IF (xval.X >= 0.0D) & (yval.X <= MAX(LONGREAL) - xval.X) OR
                     (xval.X <  0.0D) & (yval.X >= MIN(LONGREAL) - xval.X) THEN
                    xval.X := xval.X + yval.X;
                  ELSE err(206)
                  END
                ELSIF f = Set THEN
                  xval.S  := xval.S  + yval.S;
                ELSIF (f = Double) OR (f = LCard) THEN
                  xval.D := xval.D + yval.D;
                ELSE err(123)
                END;
      | minus : IF f = Card THEN
                  IF yval.C <= xval.C THEN xval.C := xval.C - yval.C
                  ELSIF yval.C - xval.C <= MaxInt THEN
                    xval.I := - VAL(INTEGER, yval.C - xval.C);
                    x.typ := inttyp; (* typ is changed! *)
                  ELSE err(207)
                  END
                ELSIF f = Int THEN
                  IF (xval.I >= 0) &
                     ((yval.I >= 0) OR (xval.I <= MaxInt + yval.I)) OR
                     (xval.I < 0) &
                     ((yval.I <  0) OR (xval.I >= MIN(INTEGER) + yval.I)) THEN
                    xval.I := xval.I - yval.I;
                  ELSE err(207)
                  END
                ELSIF f = Real THEN
                  IF (xval.R >= 0.0) &
                  ((yval.R >= 0.0) OR (xval.R <= MAX(REAL) + yval.R)) THEN
                    xval.R := xval.R - yval.R;
                  ELSIF (xval.R < 0.0) &
                  ((yval.R <  0.0) OR (xval.R >= MIN(REAL) + yval.R)) THEN
                    xval.R := xval.R - yval.R;
                  ELSE err(207)
                  END
                ELSIF f = LongReal THEN
                  IF (xval.X >= 0.0D) &
                  ((yval.X >= 0.0D) OR (xval.X <= MAX(LONGREAL) + yval.X)) THEN
                    xval.X := xval.X - yval.X;
                  ELSIF (xval.X < 0.0D) &
                  ((yval.X <  0.0D) OR (xval.X >= MIN(LONGREAL) + yval.X)) THEN
                    xval.X := xval.X - yval.X;
                  ELSE err(207)
                  END
                ELSIF f = Set THEN
                  xval.S  := xval.S  - yval.S;
                ELSIF (f = Double) OR (f = LCard) THEN
                  xval.D := xval.D - yval.D;
                ELSE err(124)
                END;
      | or :    IF f = Bool THEN xval.B := xval.B OR yval.B
                ELSE err(125)
                END;
      | eql :   IF    f = Card   THEN xval.B := xval.C  =  yval.C
                ELSIF f = Int    THEN xval.B := xval.I  =  yval.I
                ELSIF f = Real   THEN xval.B := xval.R  =  yval.R
                ELSIF f = Bool   THEN xval.B := xval.B  =  yval.B
                ELSIF f = Char   THEN xval.B := xval.Ch =  yval.Ch
                ELSIF f = Double THEN xval.B := xval.D  =  yval.D
                ELSIF f = Set    THEN xval.B := xval.S  =  yval.S
                ELSIF f = Enum   THEN xval.B := xval.Ch =  yval.Ch
                ELSIF f = LongReal THEN xval.B := xval.X = yval.X
                ELSE err(126)
                END;
                x.typ := booltyp;
      | neq :   IF    f = Card   THEN xval.B := xval.C  <>  yval.C
                ELSIF f = Int    THEN xval.B := xval.I  <>  yval.I
                ELSIF f = Real   THEN xval.B := xval.R  <>  yval.R
                ELSIF f = Bool   THEN xval.B := xval.B  <>  yval.B
                ELSIF f = Char   THEN xval.B := xval.Ch <>  yval.Ch
                ELSIF f = Double THEN xval.B := xval.D  <>  yval.D
                ELSIF f = Set    THEN xval.B := xval.S  <>  yval.S
                ELSIF f = Enum   THEN xval.B := xval.Ch <>  yval.Ch
                ELSIF f = LongReal THEN xval.B := xval.X <> yval.X
                ELSE err(126)
                END;
                x.typ := booltyp;
      | lss :   IF    f = Card   THEN xval.B := xval.C  <   yval.C
                ELSIF f = Int    THEN xval.B := xval.I  <   yval.I
                ELSIF f = Real   THEN xval.B := xval.R  <   yval.R
                ELSIF f = Bool   THEN xval.B := xval.B  <   yval.B
                ELSIF f = Char   THEN xval.B := xval.Ch <   yval.Ch
                ELSIF f = Double THEN xval.B := xval.D  <   yval.D
                ELSIF f = Enum   THEN xval.B := xval.Ch <   yval.Ch
                ELSIF f = LongReal THEN xval.B := xval.X <  yval.X
                ELSE err(126)
                END;
                x.typ := booltyp;
      | leq :   IF    f = Card   THEN xval.B := xval.C  <=  yval.C
                ELSIF f = Int    THEN xval.B := xval.I  <=  yval.I
                ELSIF f = Real   THEN xval.B := xval.R  <=  yval.R
                ELSIF f = Bool   THEN xval.B := xval.B  <=  yval.B
                ELSIF f = Char   THEN xval.B := xval.Ch <=  yval.Ch
                ELSIF f = Double THEN xval.B := xval.D  <=  yval.D
                ELSIF f = Set    THEN xval.B := xval.S  <=  yval.S
                ELSIF f = Enum   THEN xval.B := xval.Ch <=  yval.Ch
                ELSIF f = LongReal THEN xval.B := xval.X <= yval.X
                ELSE err(126)
                END;
                x.typ := booltyp;
      | gtr :   IF    f = Card   THEN xval.B := xval.C   >  yval.C
                ELSIF f = Int    THEN xval.B := xval.I   >  yval.I
                ELSIF f = Real   THEN xval.B := xval.R   >  yval.R
                ELSIF f = Bool   THEN xval.B := xval.B   >  yval.B
                ELSIF f = Char   THEN xval.B := xval.Ch  >  yval.Ch
                ELSIF f = Double THEN xval.B := xval.D   >  yval.D
                ELSIF f = Enum   THEN xval.B := xval.Ch  >  yval.Ch
                ELSIF f = LongReal THEN xval.B := xval.X  > yval.X
                ELSE err(126)
                END;
                x.typ := booltyp;
      | geq :   IF    f = Card   THEN xval.B := xval.C  >=  yval.C
                ELSIF f = Int    THEN xval.B := xval.I  >=  yval.I
                ELSIF f = Real   THEN xval.B := xval.R  >=  yval.R
                ELSIF f = Bool   THEN xval.B := xval.B  >=  yval.B
                ELSIF f = Char   THEN xval.B := xval.Ch >=  yval.Ch
                ELSIF f = Double THEN xval.B := xval.D  >=  yval.D
                ELSIF f = Set    THEN xval.B := xval.S  >=  yval.S
                ELSIF f = Enum   THEN xval.B := xval.Ch >=  yval.Ch
                ELSIF f = LongReal THEN xval.B := xval.X >= yval.X
                ELSE err(126)
                END;
                x.typ := booltyp;
      END (*CASE op*);
      WITH xx DO
        mode := conMd; typ := x.typ; val := xval;
      END;
      (* re-transform to 'conMd' *)
      IF (f # Real) & (f # LongReal) THEN SetconMd(x, LongVal(xx), x.typ)
      ELSE x := xx
      END;
    ELSE (* NOT(x.mode = conMd) & (y.mode = conMd)) *)
      IF (x.mode = stkMd) & (y.mode = stkMd) THEN
        (* if both items on stack, y must be loaded first. *)
        IF SimpleT(x) & SimpleT(y) THEN LoadD(y)
        ELSIF RealT(x) & RealT(y) THEN LoadF(y)
        END;
      END;
      PreLoad(op, x, y); (* preload x and y : No-op for real types *)
      CASE op OF
        times : IF (f = Int) OR (f = Card) OR
                   (f = CardInt) OR (f = Double) OR (f = LCard) THEN
                  Mul2(x,y)
                ELSIF (f = Real) OR (f = LongReal) THEN
                  FDyad(times,x,y)
                ELSIF f = Set THEN
                  And2(x,y)
                ELSE err(118)
                END;
      | slash : IF (f = Real) OR (f = LongReal) THEN
                  FDyad(slash,x,y)
                ELSIF f = Set THEN
                  Eor2(x,y)
                ELSE err(119)
                END;
      | div :   IF (f = Int) OR (f = Card) OR
                   (f = CardInt) OR (f = Double) OR (f = LCard) THEN
                  Div2(x,y)
                ELSE err(120)
                END;
      | rem :   IF (f = Int) OR (f = Card) OR
                   (f = CardInt) OR (f = Double) OR (f = LCard) THEN
                  err(200)
                ELSE err(121)
                END;
      | mod :   IF (f = Int) OR (f = Card) OR
                   (f = CardInt) OR (f = Double) OR (f = LCard) THEN
                  Mod2(x,y)
                ELSE err(121)
                END;
      | and :   IF x.mode = conMd THEN
                  IF x.val.B THEN
                    IF y.mode <= DregMd THEN
                      Tst1(y); setCC(y,EQ);
                    ELSIF y.mode <> cocMd THEN err(122)
                    END;
                  ELSE setCC(y,T);
                  END;
                  setCC(x,EQ);
                ELSIF y.mode <> cocMd THEN
                  IF y.typ^.form = Bool THEN
                    IF y.mode = conMd THEN
                      IF y.val.B THEN setCC(y,F) ELSE setCC(y,T) END;
                    ELSIF y.mode <= DregMd THEN
                      Tst1(y); setCC(y,EQ);
                    ELSE err(122); setCC(y,EQ);
                    END;
                  ELSE err(122); setCC(y,EQ);
                  END;
                END;
                IF y.Fjmp <> 0 THEN x.Fjmp := MergedLinks(x.Fjmp,y.Fjmp) END;
                x.CC := y.CC; x.Tjmp := y.Tjmp;
      | plus :  IF (f = Int) OR (f = Card) OR
                   (f = CardInt) OR (f = Double) OR (f = LCard) THEN
                  Add2(x,y)
                ELSIF (f = Real) OR (f = LongReal) THEN
                  FDyad(plus,x,y)
                ELSIF f = Set THEN
                  Or2(x,y)
                ELSE err(123)
                END;
      | minus : IF (f = Int) OR (f = Card) OR
                   (f = CardInt) OR (f = Double) OR (f = LCard) THEN
                  Sub2(x,y)
                ELSIF (f = Real) OR (f = LongReal) THEN
                  FDyad(minus,x,y)
                ELSIF f = Set THEN
                  Com1(y); And2(x,y)
                ELSE err(124)
                END;
      | or :    IF x.mode = conMd THEN
                  IF NOT x.val.B THEN
                    IF y.mode <= DregMd THEN
                      Tst1(y); setCC(y,EQ);
                    ELSIF y.mode <> cocMd THEN err(125)
                    END;
                  ELSE setCC(y,F);
                  END;
                  setCC(x,EQ);
                ELSIF y.mode <> cocMd THEN
                  IF y.typ^.form = Bool THEN
                    IF y.mode = conMd THEN
                      IF y.val.B THEN setCC(y,F) ELSE setCC(y,T) END;
                    ELSIF y.mode <= DregMd THEN
                      Tst1(y); setCC(y,EQ);
                    ELSE err(125); setCC(y,EQ);
                    END;
                  ELSE err(125); setCC(y,EQ);
                  END;
                END;
                IF y.Tjmp <> 0 THEN x.Tjmp := MergedLinks(x.Tjmp,y.Tjmp) END;
                x.CC := y.CC; x.Fjmp := y.Fjmp;
      | eql :   IF (f <= Double) OR (f = Set) OR
                   (f = Pointer) OR (f = Opaque) THEN
                  Cmp2(x,y); c := NE;
                ELSIF (f = Real) OR (f = LongReal) THEN
                  FDyad(eql,x,y); c := FNE;
                ELSE
                  err(126); c := NE;
                END;
                setCC(x,c);
      | neq :   IF (f <= Double) OR (f = Set) OR
                   (f = Pointer) OR (f = Opaque) THEN
                  Cmp2(x,y); c := EQ;
                ELSIF (f = Real) OR (f = LongReal) THEN
                  FDyad(neq,x,y); c := FEQ;
                ELSE
                  err(126); c := EQ;
                END;
                setCC(x,c);
      | lss :   IF (f = Int) OR (f = Double) THEN
                  Cmp2(x,y); c := GE;
                ELSIF f <= LCard THEN
                  Cmp2(x,y); c := CC;
                ELSIF (f = Real) OR (f = LongReal) THEN
                  FDyad(lss,x,y); c := FNLT;
                ELSE
                  err(126); c := CC;
                END;
                setCC(x,c);
      | leq :   IF (f = Int) OR (f = Double) THEN
                  Cmp2(x,y); c := GT;
                ELSIF f <= LCard THEN
                  Cmp2(x,y); c := HI;
                ELSIF (f = Real) OR (f = LongReal) THEN
                  FDyad(leq,x,y); c := FNLE;
                ELSIF f = Set THEN
                  LoadD(x); Com1(y); And2(x,y); c := NE;
                ELSE
                  err(126); c := HI;
                END;
                setCC(x,c);
      | gtr :   IF (f = Int) OR (f = Double) THEN
                  Cmp2(x,y); c := LE;
                ELSIF f <= LCard THEN
                  Cmp2(x,y); c := LS;
                ELSIF (f = Real) OR (f = LongReal) THEN
                  FDyad(gtr,x,y); c := FNGT;
                ELSE
                  err(126); c := LS;
                END;
                setCC(x,c);
      | geq :   IF (f = Int) OR (f = Double) THEN
                  Cmp2(x,y); c := LT;
                ELSIF f <= LCard THEN
                  Cmp2(x,y); c := CS;
                ELSIF (f = Real) OR (f = LongReal) THEN
                  FDyad(geq,x,y); c := FNGE;
                ELSIF f = Set THEN
                  LoadD(x); Com1(x); And2(x,y); c := NE;
                ELSE
                  err(126); c := CS;
                END;
                setCC(x,c);
      END (*CASE op*);
      Release(y);
    END;
  END GenOp;
  PROCEDURE GenStParam(VAR p, x : Item; fctno : Standard;
                       parno : CARDINAL; morepar : BOOLEAN);
    VAR restyp, htyp : StrPtr; f : StrForm; y, z : Item;
        r : Register; sz, hsz : WidType; shi : ShiType;
        li : LONGINT; i, lo, hi : INTEGER;
  BEGIN
    WITH x DO
      IF parno = 0 THEN (* 1. Parameter *)
        restyp := p.proc^.typ;
        IF (fctno <> Dec) & (fctno <> Inc) &
           (fctno <> Max) & (fctno <> Min) THEN SRTest(x)
        END;
        f := typ^.form;
        CASE fctno OF
          Abs :    restyp := typ; (* same type as argument type! *)
                   IF (f = Int) OR (f = Double) THEN
                     IF mode = conMd THEN
                       IF (f = Int) & (val.I = MinInt) THEN
                         err(201); val.I := 1;
                       ELSIF (f = Double) & (val.D = MinDouble) THEN
                         err(201); val.D := 1D;
                       END;
                       SetconMd(x, ABS(LongVal(x)), typ)
                     ELSE
                       Abs1(x)
                     END
                   ELSIF (f = Real) OR (f = LongReal) THEN
                     IF mode = conMd THEN
                       IF f = Real THEN
                         val.R := ABS(val.R);
                         typ := realtyp;
                       ELSE (* LongReal *)
                         val.X := ABS(val.X);
                         typ := lrltyp;
                       END
                     ELSE FMonad(Abs,x)
                     END
                   ELSE err(144)
                   END;
        | Adr :    LoadAdr(x);
        | Cap :    IF typ = chartyp THEN
                     IF mode = conMd THEN val.Ch := CAP(val.Ch)
                     ELSE Cap1(x)
                     END
                   ELSE err(144)
                   END;
        | Chr :    IF (f >= Undef) & (f <= Double) THEN
                     (* now range checks included ! *)
                     IF mode = conMd THEN
                       li := LongVal(x);
                       IF (li < 0D) OR (li > LONG(MaxChar)) THEN
                         err(138); li := 0D;
                       END;
                       SetconMd(x, li, chartyp)
                     ELSE
                       Isz(x,sz);
                       IF sz > byte THEN
                         LoadD(x);
                         IF sz = word THEN typ := inttyp END;
                         CheckClimit(x, ORD(MaxChar));
                       END
                     END
                   ELSE err(144)
                   END;
        | Float :  IF (f = Int) OR (f = Card) OR (f = CardInt) OR
                      (f = Double) THEN
                     IF mode = conMd THEN
                       li := LongVal(x); val.R := FLOAT(li);
                       typ := realtyp;
                     ELSE (* variable *)
                       IF (f = Card) OR (f = CardInt) THEN
                         LoadX(x,long); (* convert to a signed type *)
                         typ := dbltyp;
                       END;
                       (* M2TM defines the resulting type! *)
                       FMonad(fctno,x)
                     END
                   ELSE err(144)
                   END;
        | FloatD:  IF (f = Int) OR (f = Card) OR (f = CardInt) OR
                      (f = Double) THEN
                     IF mode = conMd THEN
                       li := LongVal(x); val.X := FLOATD(li);
                       typ := lrltyp;
                     ELSE (* variable *)
                       IF (f = Card) OR (f = CardInt) THEN
                         LoadX(x,long); (* convert to a signed type *)
                         typ := dbltyp;
                       END;
                       (* M2TM defines the resulting type! *)
                       FMonad(fctno,x)
                     END
                   ELSE err(144)
                   END;
        | Halt :   GenHalt(0);
        | High :   IF (mode < conMd) & (typ^.form = Array) THEN
                     IF typ^.dyn THEN
                       GetHigh(x);
                       LoadD(x);
                       (* resulting type defined by M2TM! *)
                     ELSE
                       restyp := typ^.IndexTyp;
                       IF restyp^.form = Range THEN
                         i := restyp^.max; restyp := restyp^.RBaseTyp;
                       ELSE
                         err(144); i := 0
                       END;
                       Release(x);
                       (* Note : the result type must be the same *)
                       (* ----   as the index type of the array ! *)
                       SetconMd(x, i, restyp);
                     END;
                   ELSE err(144)
                   END;
        | Max :    IF mode = typMd THEN (* transform to 'conMd' *)
                     mode := conMd;
                     CASE typ^.form OF
                       Bool :    val.B  := TRUE;
                     | Char :    val.Ch := MaxChar;
                     | Card :    val.C  := MaxCard;
                     | Int  :    val.I  := MaxInt;
                     | Enum :    val.Ch := VAL(CHAR, typ^.NofConst-1);
                     | LCard :   val.D  := 0FFFFFFFFH;
                     | Double :  val.D  := 07FFFFFFFH;
                     | Real :    val.R  := VAL(REAL, 07F7FFFFFH);
                     | LongReal: val.D0 := VAL(INTEGER, 07FEFH);
                                 val.D1 := VAL(INTEGER, 0FFFFH);
                                 val.D2 := VAL(INTEGER, 0FFFFH);
                                 val.D3 := VAL(INTEGER, 0FFFFH);
                     | Range :   SetconMd(x, typ^.max, typ^.RBaseTyp);
                     ELSE
                       err(144); SetconMd(x, 0D, undftyp);
                     END;
                     restyp := typ;
                   ELSE err(145)
                   END;
        | Min :    IF mode = typMd THEN (* transform to 'conMd' *)
                     mode := conMd;
                     CASE typ^.form OF
                       Bool :    val.B  := FALSE;
                     | Char :    val.Ch := 0C;
                     | Card :    val.C  := 0;
                     | Int  :    val.I  := VAL(INTEGER, 08000H);
                     | Enum :    val.Ch := 0C;
                     | LCard :   val.D  := 0D;
                     | Double :  val.D  := 080000000H;
                     | Real :    val.R  := VAL(REAL, 0FF7FFFFFH);
                     | LongReal: val.D0 := VAL(INTEGER, 0FFEFH);
                                 val.D1 := VAL(INTEGER, 0FFFFH);
                                 val.D2 := VAL(INTEGER, 0FFFFH);
                                 val.D3 := VAL(INTEGER, 0FFFFH);
                     | Range :   SetconMd(x, typ^.min, typ^.RBaseTyp);
                     ELSE
                       err(144); SetconMd(x, 0D, undftyp);
                     END;
                     restyp := typ;
                   ELSE err(145)
                   END;
        | Odd :    IF (f = Int) OR (f = Card) OR
                      (f = CardInt) OR (f = LCard) OR
                      (f = Double) OR (typ = addrtyp) THEN
                     IF mode = conMd THEN
                       SetconMd(x, LONG(ODD(LongVal(x))), restyp)
                     ELSE
                       LoadD(x);
                       SetconMd(y, 1D, typ);
                       And2(x,y)
                     END;
                   ELSE err(144)
                   END;
        | Ord :    IF (f >= Undef) & (f <= Double) THEN
                     (* now range checks included ! *)
                     IF mode = conMd THEN
                       li := LongVal(x);
                       IF (li < 0D) OR (li > LONG(MaxInt)) THEN
                         err(138); li := 0D;
                       END;
                       SetconMd(x, li, cardtyp);
                       (* for constants change result to CARDINAL! *)
                       restyp := cardtyp;
                     ELSE
                       Isz(x,sz);
                       IF sz = long THEN LoadD(x) ELSE LoadX(x,word)
                       END;
                       IF sz > byte THEN
                         IF sz = word THEN typ := inttyp END;
                         CheckClimit(x, MaxInt);
                       END;
                     END
                   ELSE err(144)
                   END;
        | Reg :    IF (mode = conMd) & ((f = Int) OR (f = Card)) THEN
                     (* register numbers in [0.. 15] *)
                     r := VAL(CARDINAL, WordVal(x)) MOD 16;
                     SetregMd(x, r, restyp);
                     SetbusyReg(r);
                   ELSE err(144)
                   END;
        | Short :  IF (f = Double) OR (f = LCard) THEN
                     (* now range checks included ! *)
                     IF mode = conMd THEN
                       li := LongVal(x);
                       IF (li < -32768D) OR (li > 32767D) THEN
                         err(138); li := 0D;
                       END;
                       SetconMd(x, li, inttyp);
                     ELSE
                       LoadX(x,word);
                       SetregMd(y, D0, inttyp);
                       CheckDbltoSingle(x,y); Release(y);
                     END;
                     restyp := inttyp;
                   ELSIF (f = LongReal) THEN
                     IF mode = conMd THEN
                       IF ABS(val.X) <= LONG(MAX(REAL)) THEN
                         val.R := SHORT(val.X);
                       ELSE
                         val.R := FLOAT(0); err(138);
                       END;
                       typ := realtyp;
                     ELSE FMonad(Short,x)
                     END;
                     restyp := realtyp;
                   ELSE err(144)
                   END;
        | Size :   IF mode < conMd THEN
                     IF (typ^.form = Array) & typ^.dyn THEN
                       i := typ^.ElemTyp^.size;
                       (* Caution: type is changed by GetHigh! *)
                       GetHigh(x);
                       LoadD(x);
                       Inc1(x);
                       SetconMd(y, i, typ);
                       Mul2(x,y);
                       (* resulting type defined by M2TM! *)
                     ELSE
                       (* for constants change result to CARDINAL! *)
                       Release(x);
                       restyp := cardtyp;
                       SetconMd(x, typ^.size, restyp);
                     END;
                   ELSIF mode = typMd THEN
                     restyp := cardtyp;
                     SetconMd(x, typ^.size, restyp);
                   ELSE
                     err(144); Release(x);
                     restyp := cardtyp;
                     SetconMd(x, 0D, restyp);
                   END;
        | Tsize :  IF mode = typMd THEN i := typ^.size
                   ELSE err(145); Release(x); i := 0 END;
                   (* for constants change result to CARDINAL! *)
                   restyp := cardtyp;
                   SetconMd(x, i, restyp);
(*f*)   | Long :   restyp := undftyp;
                   (* 1 parameter required, 2. parameter optional : *)
                   IF NOT morepar THEN
                     (* LONG with only one parameter : *)
                     IF (f <= Double) OR (f = Set) THEN
                       IF mode = conMd THEN
                         SetconMd(x, LongVal(x), dbltyp)
                       ELSE
                         LoadX(x,long)
                       END;
                       restyp := dbltyp;
                     ELSIF (f = Real) THEN
                       IF mode = conMd THEN
                         val.X := LONG(val.R);
                         typ := lrltyp;
                       ELSE FMonad(Long,x)
                       END;
                       restyp := lrltyp;
                     ELSE
                       err(144); Release(x);
                     END;
                   ELSE
                     (* LONG with 2 parameters : *)
                     IF (f = Int) OR (f = Card) OR (f = CardInt) THEN
                       restyp := typ (* see you later *)
                     ELSE
                       err(144); Release(x)
                     END;
                   END;
(*f*)   | Shift :  restyp := undftyp;
                   IF NOT morepar THEN err(144) (* 2 parameters required *)
                   ELSE
                     IF SimpleT(x) THEN restyp := typ; (* see you later *)
                     ELSE err(144); Release(x);
                     END;
                   END;
(*p*)   | Dec,Inc: (* 1 parameter required, 2. parameter optional : *)
                   z := x; SRTest(z);
                   f := z.typ^.form; (* f is form of the base type *)
                   IF NOT morepar THEN
                     (* DEC/INC with only one parameter : *)
                     IF (mode < conMd) & ((f >= Undef) & (f <= Double)) THEN
                       f := x.typ^.form; (* f is form of original the type *)
                       IF rngchk & ((f = Bool) OR (f = Char) OR (f = Enum) OR
                                    (f = Range)) THEN
                         IF f = Range THEN lo := x.typ^.min; hi := x.typ^.max
                         ELSIF f = Bool THEN lo := 0; hi := 1
                         ELSIF f = Char THEN lo := 0; hi := 255
                         ELSIF f = Enum THEN lo := 0; hi := x.typ^.NofConst - 1
                         END;
                         LoadX(z,word); z.typ := inttyp;
                         IF fctno = Dec THEN Dec1(z) ELSE Inc1(z) END;
                         CheckRange(z, lo, hi, 0);
                         z.typ := x.typ; (* recover original type *)
                         Move(z,x); Release(z)
                       ELSE
                         IF fctno = Dec THEN Dec1(x) ELSE Inc1(x) END
                       END;
                     ELSE err(144)
                     END
                   ELSE
                     (* DEC/INC with 2 parameters : *)
                     IF (mode < conMd) &
                        ((f >= Undef) & (f <= Double) & (f # Bool)) THEN
                       restyp := x.typ (* the original type of x! *)
                     ELSE err(144)
                     END
                   END;
(*p*)   | Excl,
          Incl :   IF NOT morepar THEN err(144) (* 2 parameters required *)
                   ELSE
                     IF (mode < conMd) & (f = Set) THEN
                       restyp := typ; (* see you later *)
                     ELSE err(144)
                     END;
                   END;
(*p*)   | Inline : IF (mode = conMd) &
                     ((f = Int) OR (f = Card) OR (f = CardInt)) THEN
                     Put16(WordVal(x))
                   ELSE err(144)
                   END;
(*p*)   | Setreg : IF NOT morepar THEN err(144) (* 2 parameters required *)
                   ELSE
                     IF (mode = conMd) & ((f = Int) OR (f = Card)) THEN
                       restyp := typ; (* see you later *)
                     ELSE err(144)
                     END;
                   END;
        | Sqrt :   IF (f = Real) OR (f = LongReal) THEN
                     restyp := typ; (* same type as argument type! *)
                     FMonad(fctno,x);
                   ELSE err(144)
                   END;
        | Trunc :  IF (f = Real) OR (f = LongReal) THEN
                     IF (mode = conMd) & (f = Real) THEN
                       IF (FLOAT(MinInt) <= val.R) &
                          (val.R <= FLOAT(MaxInt)) THEN
                         li := TRUNC(val.R);
                       ELSE
                         li := 0; err(138);
                       END;
                       SetconMd(x, li, inttyp);
                     ELSE (* variables and longreals *)
                       (* M2TM defines the resulting type! *)
                       FMonad(fctno,x)
                     END
                   ELSE err(144)
                   END;
        | TruncD,
          Entier,
          Round :  IF (f = Real) OR (f = LongReal) THEN
                     (* M2TM defines the resulting type! *)
                     FMonad(fctno,x);
                   ELSE err(144)
                   END;
(*f*)   | XCom :   restyp := typ;
                   IF SimpleT(x) THEN Com1(x)
                   ELSE err(144)
                   END;
(*f*)   | XAsh, XLsh, XRot, XMsk :
                   IF NOT morepar THEN err(144)
                   ELSE
                     IF SimpleT(x) THEN restyp := typ
                     ELSE err(144); Release(x)
                     END
                   END;
(*f*)   | Val :    (* VAL as a replacement for the type transfers *)
                   restyp := undftyp;
                   IF NOT morepar THEN err(144)
                   ELSE
                     IF (mode = typMd) THEN restyp := typ
                     ELSE err(144); Release(x)
                     END
                   END;
        | NonStand :
        END (*CASE*);
        p := x;
        p.typ := restyp;
        IF restyp = notyp THEN Release(x) END;
      ELSIF parno = 1 THEN (* 2. Parameter *)
        SRTest(x);
        f := typ^.form;
        CASE fctno OF
(*f*)     Long :   IF (p.typ <> undftyp) THEN
                     IF (f = Int) OR (f = Card) OR (f = CardInt) THEN
                       LoadD(x); x.typ := cardtyp;
                       IF (p.mode = conMd) &
                          (VAL(CARDINAL, WordVal(p)) <= MaxInt) THEN
                         li := SHIFT(LongVal(p), 16);
                         SetconMd(p, li, dbltyp);
                         LoadD(p);
                       ELSE
                         LoadD(p);
                         SetconMd(y, 16D, cardtyp);
                         p.typ := dbltyp;
                         Shi2(p,y,Lsl);   (* LSL.L *)
                       END;
                       p.typ := cardtyp;
                       Or2(p,x);          (* OR.W *)
                       p.typ := dbltyp;   (* resulting type *)
                       Release(x);
                     ELSE
                       err(144); Release(x);
                     END;
                   END;
(*f*)   | Shift :  IF (f = Int) OR (f = Card) OR (f = CardInt) THEN
                     htyp := p.typ;
                     LoadD(p);        (* load p *)
                     IF SignedT(p) THEN shi := Asl ELSE shi := Lsl END;
                     Ash2(p, x, shi); (* arithmetic/logical shift *)
                     p.typ := htyp;   (* resulting type *)
                   ELSE
                     err(144); Release(x);
                   END;
(*p*)   | Dec,Inc: IF p.typ <> notyp THEN
                     restyp := p.typ;
                     IF (f = Card) OR (f = CardInt) OR (f = Int) OR
                         (f = LCard) OR (f = Double) THEN
                       f := p.typ^.form;
                       IF rngchk & ((f = Char) OR (f = Enum) OR (f = Range)) THEN
                         z := p; (* reused for assignment *)
                         SRTest(z); Isz(z,sz);
                         LoadX(z,word);
                         IF sz < word THEN z.typ := inttyp; sz := word END;
                         IF mode = conMd THEN
                           SetconMd(x, LongVal(x), z.typ)
                         ELSE
                           LoadX(x,sz); typ := z.typ
                         END;
                         IF fctno = Inc THEN Add2(z,x) ELSE Sub2(z,x) END;
                         IF f = Range THEN lo := p.typ^.min; hi := p.typ^.max
                         ELSIF f = Char THEN lo := 0; hi := 255
                         ELSIF f = Enum THEN lo := 0; hi := p.typ^.NofConst - 1
                         END;
                         CheckRange(z, lo, hi, 0);
                         z.typ := restyp;
                         Move(z,p); Release(z)
                       ELSE
                         IF mode = conMd THEN
                           SetconMd(x, LongVal(x), restyp)
                         ELSE Isz(p,sz);
                           LoadX(x,sz); typ := restyp
                         END;
                         IF fctno = Inc THEN Add2(p,x) ELSE Sub2(p,x) END
                       END
                     ELSE err(144)
                     END
                   END;
(*p*)   | Excl,
          Incl :   IF p.typ <> notyp THEN
                     restyp := p.typ; (* original type of set *)
                     SetBaseLimits(p,lo,hi);
                     IF (typ = p.typ) OR
                        ( (restyp = bitstyp) &
                          ((typ = inttyp) OR (typ = dbltyp) OR
                          (typ = lcardtyp) OR (typ = cardinttyp)) ) THEN
                       (* recover type and size of the set. *)
                       p.typ := restyp;
                       IF SimpleC(x) THEN
                         (* constant element to include/exclude. *)
                         li := LongVal(x);
                         IF (li < LONG(lo)) OR (li > LONG(hi)) THEN
                           (* constant out of range *)
                           err(60); i := 0;
                         ELSE i := SHORT(li);
                         END;
                         li := SHIFT(1D, i);
                         IF fctno = Excl THEN li := -1D - li END;
                         SetconMd(y, li, p.typ);
                         IF fctno = Incl THEN Or2(p,y) ELSE And2(p,y) END;
                       ELSIF SimpleT(x) THEN
                         (* variable element to include/exclude. *)
                         LoadX(x,word);
                         IF typ^.size <= 2 THEN typ := inttyp END;
                         CheckRange(x,lo,hi,0);
                         GetReg(r,Dreg);
                         SetregMd(y, r, p.typ);
                         SetconMd(z, 1D, p.typ);
                         Move(z,y);
                         Shi2(y,x,Lsl);
                         IF fctno = Excl THEN Com1(y) END;
                         IF fctno = Incl THEN Or2(p,y) ELSE And2(p,y) END;
                         ReleaseReg(r);
                       ELSE
                         err(144);
                       END;
                     ELSE (*typ <> p.typ*)
                       err(144);
                     END;
                   END;
(*p*)   | Inline : IF SimpleC(x) THEN
                     Put16(WordVal(x))
                   ELSE err(144)
                   END;
(*p*)   | Setreg : IF p.typ <> notyp THEN
                     r := VAL(CARDINAL, WordVal(p)) MOD 16;
                     SetregMd(p, r, dbltyp);
                     SetbusyReg(r);
                     IF (mode = procMd) OR (typ = stringtyp) THEN MoveAdr(x,p)
                     ELSIF (typ^.size = 4) THEN Move(x,p)
                     ELSE err(144)
                     END;
                   END;
(*f*)   | XAsh, XLsh, XRot :
                   IF (f = Int) OR (f = Card) THEN
                     LoadD(p);
                     IF fctno = XAsh THEN shi := Asl (* arithmetic *)
                     ELSIF fctno = XLsh THEN shi := Lsl (* logical *)
                     ELSE shi := Rol (* rotate *)
                     END;
                     Ash2(p, x, shi) (* do the shift *)
                   ELSE
                     err(144); Release(x)
                   END;
(*f*)   | XMsk :   IF (mode = conMd) & ((f = Int) OR (f = Card)) THEN
                     i := WordVal(x);
                     IF (i < 0) OR (i > 32) THEN err(144); i := 0 END;
                     SetconMd(x, mask[i], p.typ);
                     LoadD(p);
                     And2(p, x)
                   ELSE
                     err(144); Release(x)
                   END;
(*f*)   | Val :    (* VAL as a replacement for the type transfers *)
                   ConvertTyp(p.typ, x);
                   typ := p.typ; (* resulting type *)
                   p := x;       (* resulting item *)
        ELSE (*CASE fctno OF*)
          err(64);
        END;
        IF (fctno = Dec)  OR (fctno = Inc)    OR (fctno = Excl) OR
           (fctno = Incl) OR (fctno = Inline) OR (fctno = Setreg) THEN
          (* for all standard procedures : *)
          Release(p);
          Release(x);
          p.typ := notyp; (* no result-typ for procs. *)
        ELSIF (fctno = Long) & (p.typ = undftyp) THEN
          Release(x);
        END;
      ELSE (* 3. and following Parameters *)
        SRTest(x);
        IF (fctno = Inline) THEN
          IF SimpleC(x) THEN Put16(WordVal(x))
          ELSE err(144)
          END;
        ELSE (* all other standards *)
          err(64);
        END;
        Release(x);
      END;
    END (*WITH*);
  END GenStParam;
  PROCEDURE GenStFct(fctno : Standard; parno : CARDINAL);
    VAR must : CARDINAL;
  BEGIN
    CASE fctno OF
      Abs, Adr, Cap, Chr, Float, FloatD, High, Max, Min,
      Odd, Ord, Reg, Short, Size, Tsize, Trunc, TruncD :  must := 1;
    | Excl, Incl, Setreg, Shift, Val : must := 2;
    | Dec, Inc, Long, Inline : must := 1;
    | Halt : must := 0;
    | Sqrt, Entier, Round : must := 1;
    | XAsh, XLsh, XRot, XMsk : must := 2;
    | XCom : must := 1;
    | NonStand : ;
    END (*CASE*);
    IF (fctno < NonStand) OR (must <> 0) THEN
      IF parno < must THEN err(65) END;
    END;
  END GenStFct;
END M2EM. (* Copyright Departement Informatik, ETH Zuerich, Switzerland, 1992 *)
