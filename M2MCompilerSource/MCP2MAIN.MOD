(****************************************
*                                       *
*     MODULA-2 Multi-Pass Compiler      *
*     ****************************      *
*                                       *
*     Implementation for Lilith         *
*                                       *
*                                       *
*     MCPass2:                          *
*                                       * 
*     Pass 2                            *
*     Declaration analysis              *
*                                       * 
*     Version C18 of 18.02.82           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

MODULE MCPass2; (* LG / UA *)

  (* $T-,R- *)

  IMPORT
    Storage, MCBase, MCP2IO, MCP2Ident, MCP2Reference, MCOperations;
  FROM Storage IMPORT ALLOCATE, DEALLOCATE;
  FROM MCBase IMPORT
    Idptr, Stptr, Structform, Stset, Idclass, Idset,
    Varkind, Kindvar,
    Constval, Keyarr,
    root, mainmodp, globvarnext, sysmodp, intcarptr,
    procnumber, modnamlength, maxprio, noprio, levmax,
    Symbol;
  FROM MCP2IO IMPORT
    sy,
    val,
    PutSy, PutWord, StopOutput, RestartOutput,
    Error, ErrorLS,
    spix,
    GetSy, PutGetSy,
    AsciiSetPos, AsciiRead,
    SkipConstant, SkipType,
    GetModuleKey, DefModStatus, TermInOut;
  FROM MCP2Reference IMPORT
    Reference, EndReference, InitRef, TermRef;
  FROM MCP2Ident IMPORT
    Locate,
    NewImpList, TermImpList, EnterImpList,
    MarkScope, ReleaseScope,
    MsEntry,
    EnterList, EnterId,
    SearchInBlock, SearchId,
    ExportSearch, SymModSearch, GlobalKnown;

  MODULE ModulInitialisation; 
    (* $T- *)

    FROM MCP2IO IMPORT PutSy, PutWord;
    FROM MCBase IMPORT Symbol, Idptr;

    EXPORT
      MarkInitBlock, ReleaseInitBlock, EnterInitModule,
      ToInitModule, InitModules, MustInit, Initrange,
      ResetModuleInit;

    CONST initmax = 20;
          blevelmax = 20; 

    TYPE Initrange = [0..initmax];

    VAR inittab : ARRAY Initrange OF 
                    RECORD toinit : BOOLEAN;
                      mptr : Idptr; 
                    END;
        blockdispl : ARRAY [1..blevelmax] OF Initrange; 
        blevel : CARDINAL; 
        inittop : CARDINAL;

    PROCEDURE MarkInitBlock;
    BEGIN
      INC(blevel);
      IF blevel > blevelmax THEN HALT END;
      blockdispl[blevel] := inittop;
    END MarkInitBlock;

    PROCEDURE ReleaseInitBlock;
    BEGIN 
      inittop := blockdispl[blevel];
      DEC(blevel); 
    END ReleaseInitBlock;

    PROCEDURE EnterInitModule(ip : Idptr; VAR initix : Initrange); 
    BEGIN INC(inittop); 
      IF inittop > initmax THEN HALT END;
      initix := inittop; 
      WITH inittab[inittop] DO toinit := FALSE; mptr := ip END;
    END EnterInitModule;

    PROCEDURE ToInitModule(initix : Initrange); 
    BEGIN 
      WITH inittab[initix] DO
        toinit := TRUE;
        PutSy(proceduresy); PutWord(mptr);
      END 
    END ToInitModule; 

    PROCEDURE InitModules;
      VAR i : CARDINAL;
    BEGIN i := blockdispl[blevel] + 1;
      WHILE i <= inittop DO 
        WITH inittab[i] DO
          IF toinit THEN PutSy(call); PutSy(namesy); PutWord(mptr); 
            PutSy(lparent); PutSy(rparent); 
          END;
        END; INC(i);
      END 
    END InitModules;

    PROCEDURE MustInit() : BOOLEAN; 
      VAR i : CARDINAL;
    BEGIN i := blockdispl[blevel] + 1;
      WHILE i <= inittop DO
        IF inittab[i].toinit THEN RETURN TRUE END;
        INC(i);
      END;
      RETURN blevel = 1; (* global modules must always be initialised *)
    END MustInit; 

    PROCEDURE ResetModuleInit;
    BEGIN
      inittop := 0;
      blevel := 0;
    END ResetModuleInit;

    (* $T= *)
  END ModulInitialisation;

  PROCEDURE FAmong(sp: Stptr; forms: Stset): BOOLEAN;
  BEGIN
    IF sp = NIL THEN RETURN FALSE END;
    WITH sp^ DO
      RETURN (form IN forms) OR
             (form = subranges) AND FAmong(scalp,forms);
    END;
  END FAmong;

  PROCEDURE QualIdent(klset: Idset; errnum: CARDINAL; VAR ip: Idptr);
  BEGIN (* sy = ident *)
    SearchId(ip); 
    LOOP
      GetSy;
      IF sy <> period THEN EXIT END;
      IF (ip <> NIL) AND (ip^.klass = mods) THEN
        GetSy;
        ExportSearch(ip^.expp,ip); (* new value for ip *)
      ELSE ErrorLS(105); GetSy;
      END;
    END;
    IF ip = NIL THEN
      ErrorLS(errnum);
    ELSIF NOT (ip^.klass IN klset) THEN
      ErrorLS(103); (* identifier not of expected klass *)
      ip := NIL;
    END;
  END QualIdent;

  PROCEDURE InitId(ip: Idptr; cl: Idclass);
    (* initialisation of identifier record *)
  BEGIN
    WITH ip^ DO
      name := spix; (* from MCP2IO *)
      globmodp := mainmodp;
      idtyp := NIL; (* = nxtidp *)
      klass := cl; link := NIL;
    END;
  END InitId;

  CONST scalars = Stset{enums,bools,chars,ints,cards,subranges};
        oneword = 1;                 (* space used for addressing *)
        doubleword = 2 * oneword;
        procmarkspace = 4 * oneword; (* space used for procedure mark *)
        maxchar = 377B;    (* maximal character value *)
        minint = 100000B;  (* minimal integer value *)
        maxint = 77777B;   (* maximal integer value *)
        maxcard = 177777B; (* maximal cardinal value *)

  VAR nestlevel : CARDINAL; (* nesting level *)
      symmod : BOOLEAN; (* current module is symbol module *)
      defmod : BOOLEAN; (* module is definition module *)
      impl: BOOLEAN; (* implementation expected *)
      oldlist: Idptr; (* list of identifiers to implement *)
      proccount : CARDINAL; (* counter of procedures *)

  MODULE ConstDefinition; 

    FROM Storage IMPORT ALLOCATE;
    FROM MCP2IO IMPORT
      sy, val, length, Error, ErrorLS, GetSy, PutGetSy;
    FROM MCBase IMPORT
      Idptr, Stptr, Idclass, Idset, Structform, Stset,
      Constval, Symbol,
      intptr, cardptr, intcarptr, realptr, charptr, boolptr,
      bitsetptr, strptrs;
    FROM MCOperations IMPORT RelOp, AddOp, MulOp, NotOp;
    FROM TypeDefinition IMPORT ArrayStruct;
    IMPORT FAmong, QualIdent, symmod, scalars, maxint;

    EXPORT ConstantVal, ConstantRange; 

    TYPE Constform = RECORD
                       ctp: Stptr;
                       cval: Constval;
                     END; 

    VAR forms : Stset;
        err : BOOLEAN;

    PROCEDURE SetConstructor(VAR setptr: Stptr; VAR setval: Constval); 
      VAR styp,ctyp : Stptr;
          c1,c2 : CARDINAL;
          smin,smax : CARDINAL; 
          setpat : BITSET; (* set pattern *)

      PROCEDURE RangeSet(rmin, rmax: CARDINAL): BITSET;
        (* construct a set representation of a range *)
        VAR bitval : CARDINAL;
      BEGIN (* RangeSet *)
        (* assume rmax >= rmin *)
        rmin := rmax - rmin;
        rmax := 15 - rmax;
        bitval := 1; (* at least one element in range *)
        WHILE rmin > 0 DO bitval := bitval * 2 + 1; DEC(rmin) END;
        WHILE rmax > 0 DO bitval := bitval * 2; DEC(rmax) END;
        RETURN BITSET(bitval);
      END RangeSet;

    BEGIN (* SetConstructor *)
      smin := 0; smax := 15; setpat := {};
      IF FAmong(setptr,Stset{sets}) THEN
        styp := setptr^.basep;
      ELSE ErrorLS(99);
        styp := NIL; setptr := NIL;
      END;
      IF styp <> NIL THEN
        WITH styp^ DO
          CASE form OF
            subranges:
              styp := scalp;
              (* assume INTEGER(min) > 0 for base type INTEGER *)
              IF min > smin THEN smin := min END;
              IF max < smax THEN smax := max END;
           |enums: IF cstnr < smax THEN smax := cstnr END
           |bools: smax := 1
          ELSE styp := NIL; 
          END; (* CASE *)
        END; (* WITH *) 
      END;
      GetSy; (* lconbr *) 
      WHILE sy <> rconbr DO 
        ConstantRange(ctyp,c1,c2); 
        IF (styp = NIL) AND FAmong(ctyp,Stset{enums,bools,cards}) THEN
          styp := ctyp
        END;
        IF (styp <> NIL) AND
           ((ctyp=intcarptr) AND ((styp=cardptr) OR (styp=intptr)) OR
            (styp=ctyp)) THEN 
          IF (c1 < smin) OR (c2 > smax) OR (ctyp = intptr) THEN
            ErrorLS(98); 
          ELSE
            setpat := setpat + RangeSet(c1,c2);
          END;
        ELSE ErrorLS(97); 
        END;
        IF sy = comma THEN GetSy END;
      END;
      GetSy; (* rconbr *) 
      setval.value := CARDINAL(setpat);
    END SetConstructor; 

    PROCEDURE ConstExpression(VAR cf: Constform);
      (* expression in constant definitions *)
      VAR cf1: Constform;
          op : Symbol;
          res : Constval;
          tp, tp1 : Stptr;

      PROCEDURE Compatible(tp1,tp2: Stptr): BOOLEAN;          
        (* compare on type compatibility in constant expressions *) 
      BEGIN 
        RETURN
          (tp1=tp2) OR (tp1=NIL) OR (tp2=NIL) OR 
          (tp1=intcarptr) AND ((tp2=cardptr) OR (tp2=intptr)) OR 
          (tp2=intcarptr) AND ((tp1=cardptr) OR (tp1=intptr));  
      END Compatible;   
 
      PROCEDURE ConstSimpleExpression(VAR cf: Constform);
        (* simple expression in constant definitions *)
        VAR cf1 : Constform;
            op : Symbol;
            sign : BOOLEAN;

        PROCEDURE ConstTerm(VAR cf: Constform); 
          (* term in constant definitions *)  
          VAR cf1 : Constform; 
              op : Symbol; 

          PROCEDURE ConstFactor(VAR cf: Constform);  
            (* factor in constant definitions *)
            VAR ip : Idptr;
          BEGIN
            WITH cf DO ctp := NIL; cval.value := 0 END;
            IF (sy >= intcon) AND (sy <= stringcon) THEN
              WITH cf DO
                WITH cval DO
                  value := val;
                  CASE sy OF
                    intcon: ctp := intptr;
                   |intcarcon: ctp := intcarptr;
                   |cardcon: ctp := cardptr;
                   |realcon: ctp := realptr;
                   |charcon: ctp := charptr;
                   |stringcon:
                      IF (length > 20) OR (strptrs[length] = NIL) THEN
                        ctp := ArrayStruct(0,length-1,cardptr,charptr);
                        IF length <= 20 THEN strptrs[length] := ctp END;
                      ELSE
                        ctp := strptrs[length];
                      END;
                  END;
                  IF symmod AND (sy = cardcon) THEN (* get type identifier *)
                    GetSy;
                    QualIdent(Idset{types},73,ip);
                    ctp := ip^.idtyp;
                  ELSE GetSy;
                  END;
                END; (* WITH *)
              END; (* WITH *)
            ELSIF sy = ident THEN
              (* constant or set constructor with type identifier *)
              QualIdent(Idset{consts,types},73,ip);
              IF sy = lconbr THEN (* set constructor *)
                IF (ip <> NIL) AND (ip^.klass = types) THEN
                  cf.ctp := ip^.idtyp;
                ELSIF ip <> NIL THEN ErrorLS(103);
                END;
                SetConstructor(cf.ctp,cf.cval);
              ELSE
                IF (ip <> NIL) AND (ip^.klass = consts) THEN
                  WITH ip^ DO
                    cf.ctp := idtyp;
                    IF idtyp = realptr THEN (* make a copy of the real value *)
                      NEW(cf.cval.rvalue);
                      cf.cval.rvalue^ := cvalue.rvalue^;
                    ELSIF idtyp = NIL THEN ErrorLS(73);
                    ELSE cf.cval := cvalue;
                    END;
                  END;
                ELSIF ip <> NIL THEN ErrorLS(103); 
                END;
              END;
            ELSIF sy = lconbr THEN (* bitset *)
              cf.ctp := bitsetptr;
              SetConstructor(cf.ctp,cf.cval);
            ELSIF sy = lparent THEN
              GetSy;
              ConstExpression(cf);
              GetSy;
            ELSIF sy = notsy THEN
              GetSy;
              ConstFactor(cf);
              IF FAmong(cf.ctp,Stset{bools}) THEN
                NotOp(cf.cval,cf.cval);
              ELSE ErrorLS(140);
              END;
            END;
          END ConstFactor;

        BEGIN       
          ConstFactor(cf); 
          WHILE (sy >= andsy) AND (sy <= modsy) DO
            op := sy; 
            GetSy;
            ConstFactor(cf1); 
            IF cf.ctp = NIL THEN cf := cf1;
            ELSE
              WITH cf DO 
                IF (ctp = intcarptr) AND 
                   FAmong(cf1.ctp,Stset{ints,cards}) THEN
                  ctp := cf1.ctp;
                END;
                IF Compatible(ctp,cf1.ctp) THEN
                  CASE op OF
                    andsy: forms := Stset{bools};
                   |times: forms := Stset{ints,cards,sets,reals};
                   |slash: forms := Stset{sets,reals};
                   |divsy,modsy: forms := Stset{ints,cards};
                  END;
                  IF FAmong(ctp,forms) THEN
                    MulOp(cval,cf1.cval,cval,op,ctp,err);
                    IF err THEN ErrorLS(94) END;
                  ELSE ErrorLS(140); 
                  END; 
                ELSE ErrorLS(143); 
                END; 
              END; (* WITH *) 
            END; 
          END; (* WHILE *) 
        END ConstTerm; 

      BEGIN 
        sign := (sy = minus) OR (sy = plus);
        IF sign THEN op := sy; GetSy; END;
        ConstTerm(cf);
        IF sign THEN
          WITH cf DO
            IF (ctp=intptr) OR (ctp=intcarptr) OR (ctp=realptr) THEN
              IF op = minus THEN
                IF ctp = realptr THEN cf1.cval.rvalue := NIL;
                ELSE cf1.cval.value := 0;
                END;
                AddOp(cf1.cval,cval,cval,minus,ctp,err);
                IF err THEN ErrorLS(94) END;
              END;
            ELSIF ctp = cardptr THEN
              IF op = minus THEN ErrorLS(121) END;
            ELSE ErrorLS(121);
            END; 
          END; 
        END;
        WHILE (sy >= plus) AND (sy <= orsy) DO 
          op := sy;
          GetSy;
          ConstTerm(cf1);
          IF cf.ctp = NIL THEN cf := cf1;
          ELSE
            WITH cf DO 
              IF (ctp = intcarptr) AND
                 FAmong(cf1.ctp,Stset{ints,cards}) THEN
                ctp := cf1.ctp;
              END;
              IF Compatible(ctp,cf1.ctp) THEN
                CASE op OF
                  orsy: forms := Stset{bools};
                 |plus,minus: forms := Stset{ints,cards,sets,reals};
                END;
                IF FAmong(ctp,forms) THEN
                  AddOp(cval,cf1.cval,cval,op,ctp,err);
                  IF err THEN ErrorLS(94) END; 
                ELSE ErrorLS(140); 
                END; 
              ELSE ErrorLS(143); 
              END; 
            END; (* WITH *) 
          END; 
        END; (* WHILE *) 
      END ConstSimpleExpression;   

    BEGIN
      ConstSimpleExpression(cf);
      IF (sy >= eql) AND (sy <= insy) THEN
        res.value := CARDINAL(FALSE); (* initial value *)
        op := sy;
        GetSy;
        ConstSimpleExpression(cf1);
        tp := cf.ctp;
        tp1 := cf1.ctp;    
        IF op = insy THEN
          IF FAmong(tp1,Stset{sets}) THEN
            tp1 := tp1^.basep;
            IF Compatible(tp,tp1) THEN
              RelOp(cf.cval,cf1.cval,res,insy,tp,err); 
              IF err THEN ErrorLS(94) END;
            ELSE ErrorLS(142); 
            END;
          ELSE ErrorLS(149);
          END;
        ELSIF Compatible(tp,tp1) THEN
          IF tp = intcarptr THEN tp := tp1 END;
          CASE op OF
            eql,neq: forms := Stset{sets,pointers,reals} + scalars;
           |geq,leq: forms := Stset{sets,reals} + scalars;
           |grt,lss: forms := Stset{reals} + scalars;
          END;
          IF FAmong(tp,forms) THEN 
            RelOp(cf.cval,cf1.cval,res,op,tp,err);
            IF err THEN ErrorLS(94) END;
          ELSE ErrorLS(140);
          END;
        ELSE ErrorLS(143) 
        END; 
        cf.ctp := boolptr; 
        cf.cval := res; 
      END; 
    END ConstExpression; 

    PROCEDURE Constant(VAR c: Constform);
    BEGIN
      ConstExpression(c);
      WITH c DO
        IF ((ctp=intptr) OR (ctp=cardptr)) AND (cval.value<=maxint) THEN
          ctp := intcarptr;
        END;
      END;
    END Constant;

    PROCEDURE ConstantRange(VAR ctyp: Stptr; VAR cmin,cmax: CARDINAL);
      VAR c1,c2: CARDINAL; 
          tp : Stptr;
          c : Constform;
    BEGIN (* ConstantRange *)
      Constant(c);
      tp := c.ctp; c1 := c.cval.value; c2 := c1;
      IF sy = range THEN
        GetSy;
        IF FAmong(tp,scalars) THEN
          Constant(c);
          WITH c DO
            IF tp = intcarptr THEN
              IF FAmong(ctp,Stset{ints,cards}) THEN tp := ctp END;
            ELSIF ctp = intcarptr THEN
              IF FAmong(tp,Stset{ints,cards}) THEN ctp := tp END;
            END;
            IF tp = ctp THEN
              c2 := cval.value;
              IF tp = intptr THEN
                IF INTEGER(c2) < INTEGER(c1) THEN c2 := c1; ErrorLS(95) END;
              ELSE
                IF c2 < c1 THEN c2 := c1; ErrorLS(95) END;
              END;
            ELSE ErrorLS(95)
            END;
          END;
        ELSE ErrorLS(96); 
          Constant(c);
        END;
      END;
      ctyp := tp;
      cmin := c1; cmax := c2; 
    END ConstantRange; 

    PROCEDURE ConstantVal(VAR fsp: Stptr; VAR fval: Constval); 
      VAR c: Constform; 
    BEGIN Constant(c);
      WITH c DO fsp := ctp; fval := cval END;
    END ConstantVal;

  END ConstDefinition;

  MODULE TypeDefinition;

    FROM Storage IMPORT ALLOCATE, DEALLOCATE;
    FROM MCBase IMPORT
      levmax,
      Idptr, Stptr, Idclass, Idset, Structform, Stset,
      Symbol,
      Varkind, Kindvar, Recpart,
      intptr, cardptr, intcarptr;
    FROM MCP2IO IMPORT
     sy, spix, val, Error, ErrorLS,
     GetSy, PutGetSy;
    FROM MCP2Ident IMPORT
      Locate, EnterList, EnterId, EnterForward,
      SearchId, SearchInBlock, MsEntry;
    FROM MCP2Reference IMPORT Reference;
    FROM ConstDefinition IMPORT ConstantRange;
    IMPORT
      symmod, nestlevel,
      oneword, doubleword, procmarkspace, scalars,
      maxchar, minint, maxint, maxcard,
      FAmong, QualIdent, InitId;

    EXPORT ActualTyp, ArrayStruct, ParamList;

    PROCEDURE RangeTypeAndBounds(sp: Stptr; VAR rsp: Stptr; VAR rmin, rmax: CARDINAL);
    BEGIN (* RangeTypeAndBonds *)
      rsp := sp;
      rmin := 0; rmax := 0;
      IF rsp <> NIL THEN
        WITH rsp^ DO
          CASE form OF
            enums : rmax := cstnr;
          | bools : rmax := 1;
          | chars : rmax := maxchar;
          | ints  : rmin := minint; rmax := maxint;
          | cards : rmax := maxcard; rsp := cardptr; (* might be intcarptr *)
          | subranges : rmin := min; rmax := max; rsp := scalp;
          ELSE (* no scalar type *)
            ErrorLS(109);
            rsp := NIL;
          END; (* CASE *)
        END; (* WITH *) 
      END; (* IF *) 
    END RangeTypeAndBounds;

    PROCEDURE Subrange(cp: Stptr; c1,c2: CARDINAL): Stptr; 
      VAR sp : Stptr; 
    BEGIN 
      NEW(sp,subranges);
      WITH sp^ DO 
        size := oneword;
        stidp := NIL; inlist := FALSE;
        form := subranges; scalp := cp; 
        min := c1; max := c2; 
      END;
      RETURN sp 
    END Subrange; 

    PROCEDURE ArrayStruct(imin,imax: CARDINAL; ind,el: Stptr): Stptr;
      VAR sp : Stptr;
          idiff : CARDINAL; (* index difference *)
          mc, mv : CARDINAL; (* help for multiplication *)
    BEGIN
      NEW(sp,arrays);
      WITH sp^ DO
        IF el <> NIL THEN
          (* assume that 'imin <= imax' in relation belonging to type *)
          IF FAmong(ind,Stset{ints}) THEN
            IF (INTEGER(imin) < 0) AND (INTEGER(imax) >= 0) THEN
              idiff := maxcard - imin + 1 + imax;
            ELSE (* both bounds with same sign *)
              idiff := imax - imin;
            END;
          ELSE
            idiff := imax - imin;
          END;
          (* number of elements is 'idiff + 1' *)
          IF FAmong(el,Stset{chars}) THEN (* character arrays are packed and aligned *)
            size := idiff DIV 2 + 1;
          ELSE (* multiply with element size *)
            size := 0;
            IF idiff < maxcard THEN
              mc := idiff + 1;
              IF mc < el^.size THEN mv := mc; mc := el^.size ELSE mv := el^.size END;
              WHILE (mv > 0) AND (size <= maxcard - mc) DO DEC(mv); INC(size,mc) END;
              IF mv > 0 THEN ErrorLS(100) END;
            ELSE ErrorLS(100);
            END;
          END;
        ELSE size := 0;
        END;
        stidp := NIL; inlist := FALSE;
        form := arrays; dyn := FALSE; elp := el;
        IF FAmong(ind,Stset{subranges}) THEN ixp := ind
        ELSE ixp := Subrange(ind,imin,imax);
        END;
      END;
      RETURN sp;
    END ArrayStruct;

    PROCEDURE ParamList(withid: BOOLEAN; VAR paraddr: CARDINAL;
                        VAR procp: Stptr);
      VAR parh,part,parn : Idptr;
          ftp,sp : Stptr;
          rk : Idclass;
          vk : Varkind;
          cpar : BOOLEAN; (* parameters are copy parameters *)
          indac : BOOLEAN; (* indirect access to parameter value *)
          space : CARDINAL; (* space used for entry on stack *)

      PROCEDURE ParamId;
        VAR ip : Idptr;
      BEGIN
        NEW(ip,vars);
        InitId(ip,vars);
        WITH ip^ DO
          indaccess := FALSE;
          vkind := vk;
          IF nestlevel <= levmax THEN vlevel := nestlevel;
          ELSE vlevel := levmax;
          END;
          state := local; vlink := NIL;
        END;
        IF parh = NIL THEN parh := ip ELSE part^.vlink := ip END;
        part := ip;
        IF withid THEN EnterId(ip) END;
      END ParamId;

    BEGIN
      paraddr := procmarkspace;
      parh := NIL; part := NIL;
      rk := pures;
      IF sy = lparent THEN GetSy;
        WHILE sy <> rparent DO
          IF sy = varsy THEN GetSy; vk := varparam ELSE vk := valparam END;
          parn := part; (* mark new list of parameters *)
          IF withid THEN 
            WHILE sy <> colon DO ParamId; GetSy END;
            GetSy; (* colon *)
          ELSE ParamId;
          END;
          FormalTyp(ftp);
          space := oneword;
          cpar := FALSE;
          IF FAmong(ftp,Stset{reals,records,arrays}) THEN
            indac := TRUE;
            IF (ftp^.form = arrays) AND ftp^.dyn THEN
              space := doubleword;
              IF vk = valparam THEN
                cpar := TRUE;
              END;
            ELSIF vk = valparam THEN
              IF FAmong(ftp,Stset{reals}) THEN
                indac := FALSE;
                space := doubleword; (* expressions ! *)
              ELSE (* arrays, records *)
                cpar := TRUE;
              END;
            END;
          ELSE
            indac := vk <> valparam;
          END;
          (* allocation and type entry *)
          IF parn = NIL THEN parn := parh ELSE parn := parn^.vlink END;
          WHILE parn <> NIL DO
            WITH parn^ DO
              idtyp := ftp;
              IF cpar THEN vkind := copyparam END;
              indaccess := indac;
              vaddr := paraddr;
              INC(paraddr,space);
              IF withid THEN Reference(parn) END;
              parn := vlink;
            END;
          END;
        END; (* WHILE *)
        GetSy; (* rparent*)
        IF sy = colon THEN GetSy;
          rk := funcs;
          SimpleTyp(ftp);
          IF NOT FAmong(ftp,Stset{enums,bools,chars,ints,cards,words,reals,
                                  subranges,pointers,sets,hides}) THEN
            ErrorLS(88) 
          END;
        END;
      END;
      IF rk = pures THEN NEW(sp,proctypes,pures)
      ELSE NEW(sp,proctypes,funcs)
      END;
      WITH sp^ DO
        size := oneword; stidp := NIL; inlist := FALSE;
        form := proctypes; fstparam := parh;
        rkind := rk;
        IF rk = funcs THEN funcp := ftp END;
      END;
      procp := sp;
    END ParamList;

    PROCEDURE SimpleTyp(VAR trf: Stptr);
      VAR lsp: Stptr;
          lip, tref: Idptr;
          c1 : CARDINAL;

    PROCEDURE SubrangeTyp(VAR sp: Stptr);
      VAR cp, tp : Stptr;
          cmin, cmax : CARDINAL;
          rmin, rmax : CARDINAL;
    BEGIN (* SubrangeTyp *)
      RangeTypeAndBounds(sp,tp,rmin,rmax);
      GetSy; (* skip lbrack *)
      ConstantRange(cp,cmin,cmax);
      IF tp = NIL THEN (* subrange without preceding type *)
        IF cp = intcarptr THEN cp := cardptr END; (* base type CARDINAL *)
      ELSE (* check values with preceding type *)
        IF (tp=intptr) AND ((cp=tp) OR (cp=intcarptr)) THEN
          IF (INTEGER(rmin) > INTEGER(cmin)) OR (INTEGER(rmax) < INTEGER(cmax)) THEN
            ErrorLS(102);
          END;
          cp := tp;
        ELSIF (tp=cp) OR (tp=cardptr) AND (cp=intcarptr) THEN
          IF (rmin > cmin) OR (rmax < cmax) THEN ErrorLS(102) END;
          cp := tp;
        ELSE ErrorLS(102);
        END;
      END;
      sp := Subrange(cp,cmin,cmax);
      GetSy; (* skip rbrack *)
    END SubrangeTyp;

    BEGIN (* SimpleTyp *)
      IF sy = lparent THEN GetSy; c1 := 0;
        NEW(lsp,enums); 
        WITH lsp^ DO form := enums; stidp := NIL; inlist := FALSE END;
        tref := NIL;
        WHILE sy <> rparent DO
          NEW(lip,consts); 
          InitId(lip,consts);
          WITH lip^ DO
            idtyp := lsp;
            IF symmod THEN GetSy; cvalue.value := val;
            ELSE cvalue.value := c1;
            END;
          END;
          EnterList(tref,lip); 
          SearchInBlock(lip); (* new value for lip *) 
          IF (lip <> NIL) AND (lip^.klass <> unknown) THEN Error(72) END; 
          GetSy;
          INC(c1);
        END;
        WITH lsp^ DO
          size := oneword;
          fcstp := tref; cstnr := c1 - 1; (* c1 is number of elements *)
        END;
        MsEntry(tref);
        GetSy;
      ELSIF sy = ident THEN QualIdent(Idset{types},73,lip); 
        IF lip = NIL THEN lsp := NIL;
        ELSE
          lsp := lip^.idtyp;
          IF lsp = NIL THEN ErrorLS(74) END;
        END;
        IF sy = lbrack THEN SubrangeTyp(lsp) END;
      ELSIF sy = lbrack THEN (* subrange *)
        lsp := NIL;
        SubrangeTyp(lsp);
      END;
      trf := lsp; 
    END SimpleTyp;

    PROCEDURE PointerTyp(VAR trf: Stptr); 
      VAR lip: Idptr;
          lsp,t1rf: Stptr;
    BEGIN
      NEW(lsp,pointers); trf := lsp;
      WITH lsp^ DO
        size := oneword; stidp := NIL; inlist := FALSE; 
        form := pointers; elemp := NIL; 
      END;
      IF sy = ident THEN
        (* search for module name first *)
        SearchId(lip);
        IF (lip <> NIL) AND (lip^.klass = mods) THEN
          QualIdent(Idset{types},73,lip);
          IF lip <> NIL THEN
            lsp^.elemp := lip^.idtyp;
            IF lip^.idtyp = NIL THEN ErrorLS(74) END;
          END;
        ELSE
          (* search for a local declared name *)
          SearchInBlock(lip);
          IF (lip = NIL) OR (lip^.klass = unknown) THEN
            EnterForward(lsp);
          ELSE
            IF lip^.klass = types THEN
              lsp^.elemp := lip^.idtyp;
              IF lip^.idtyp = NIL THEN Error(74) END;
            ELSE Error(73);
            END;
          END;
          GetSy;
          IF sy = period THEN (* overread incorrect qualident *)
            ErrorLS(105);
            WHILE sy = period DO GetSy; GetSy; END;
          END;
        END;
      ELSE ActualTyp(t1rf); lsp^.elemp := t1rf; END;
    END PointerTyp; 

    PROCEDURE RecordTyp(VAR trf: Stptr);
      VAR vrf: Stptr;
          frf: Idptr; 
          offset: CARDINAL;
          lsp: Stptr;


      PROCEDURE FieldList(VAR offs: CARDINAL; VAR vtabref: Stptr); 
        VAR offset, offse, maxoffset: CARDINAL;
            ttp: Stptr;
            tagref, svtrf, cxv: Stptr;
            x, xh, xt: Idptr;
            ctp : Stptr;           (* type of new current case labels *)
            c1, c2: CARDINAL;      (* bound values of current case labels *)
            ltp : Stptr;           (* expected type of case labels *)
            lmin, lmax : CARDINAL; (* minimal and maximal value of case labels *)

        PROCEDURE EnterVariant(VAR vrf: Stptr; val: CARDINAL);
          VAR varref: Stptr;
        BEGIN NEW(varref,records,variantpart);
          WITH varref^ DO
            stidp := NIL; inlist := FALSE;
            form := records; rpart := variantpart; nxtvarp := NIL;
            subtagp := cxv; (* temporary link *)
            varval := val;
          END;
          cxv := varref; vrf := varref; 
        END EnterVariant; 

        PROCEDURE VariantField(val: CARDINAL); 
          VAR lsp: Stptr; goon: BOOLEAN;
        BEGIN goon := TRUE; 
          WITH tagref^ DO 
            IF fstvarp = NIL THEN EnterVariant(fstvarp,val); goon := FALSE; 
            ELSE lsp := fstvarp; END; 
          END;
          WHILE goon DO 
            WITH lsp^ DO
              IF varval = val THEN ErrorLS(93); goon := FALSE;
              ELSIF nxtvarp = NIL THEN EnterVariant(nxtvarp,val); goon := FALSE;
              ELSE lsp := nxtvarp END;
            END;
          END;
        END VariantField; 

        PROCEDURE IdentComplete(ip: Idptr); 
          VAR sz: CARDINAL; 
        BEGIN (* offset, ttp from FieldList *)
          IF ttp <> NIL THEN sz := ttp^.size ELSE sz := 0 END;
          WHILE ip <> NIL DO
            WITH ip^ DO
              ip := nxtidp; idtyp := ttp;
              fldaddr := offset;
              IF maxcard - sz >= offset THEN INC(offset,sz);
              ELSE (* record structure too large *)
                ErrorLS(100);
              END;
            END;
          END;
        END IdentComplete;

        PROCEDURE DisposeCase(fsp: Stptr);
          VAR lsp,lsp1: Stptr;
        BEGIN 
          IF fsp <> NIL THEN
            lsp := fsp^.fstvarp;
            WHILE lsp <> NIL DO 
              IF lsp^.nxtvarp = NIL THEN DisposeCase(lsp^.subtagp); 
              ELSIF lsp^.nxtvarp^.subtagp <> lsp^.subtagp THEN
                DisposeCase(lsp^.subtagp);
              END;
              lsp1 := lsp; lsp := lsp^.nxtvarp; 
              DISPOSE(lsp1,records,variantpart);
            END;
            IF fsp^.elsevarp <> NIL THEN DisposeCase(fsp^.elsevarp^.subtagp); 
              DISPOSE(fsp^.elsevarp,records,variantpart); 
            END;
            lsp := fsp; DISPOSE(lsp,records,tagfield);
          END;
        END DisposeCase;

      BEGIN (*FieldList*) 
        offset := offs; tagref := NIL;
        DisposeCase(vtabref); 
        IF sy = casesy THEN GetSy;
          xh := NIL; 
          IF sy = ident THEN (* explicit tagfield *)
            NEW(xh,fields);
            InitId(xh,fields);
            EnterList(frf,xh); GetSy; 
          END;
          (* sy = colon ;  inserted by pass1 *) 
          GetSy;
          QualIdent(Idset{types},91,x); 
          IF x = NIL THEN ttp := NIL;
          ELSE ttp := x^.idtyp;
            IF ttp = NIL THEN ErrorLS(74) END;
          END;
          IF xh <> NIL THEN IdentComplete(xh) END;
          NEW(tagref,records,tagfield); 
          WITH tagref^ DO 
            stidp := NIL; inlist := FALSE;
            form := records;
            rpart := tagfield; fstvarp := NIL;
            tagtyp := ttp; elsevarp := NIL;
          END;
          RangeTypeAndBounds(ttp,ltp,lmin,lmax);
          maxoffset := offset; cxv := NIL;
          WHILE sy = ofsy DO
            GetSy;
            IF symmod THEN (* get variant labels *)
              REPEAT VariantField(val); GetSy UNTIL sy = colon;
            ELSE (* process variant labels *)
              REPEAT
                ConstantRange(ctp,c1,c2);
                IF ltp = NIL THEN RangeTypeAndBounds(ctp,ltp,lmin,lmax) END; 
                IF (ltp = intptr) AND ((ctp = intcarptr) OR (ctp = intptr)) THEN
                  IF (INTEGER(c1) < INTEGER(lmin)) OR
                     (INTEGER(c2) > INTEGER(lmax)) THEN
                    ErrorLS(110);
                  END;
                  VariantField(c1);
                  WHILE INTEGER(c1) < INTEGER(c2) DO
                    IF c1 = maxcard THEN c1 := 0 ELSE INC(c1) END;
                    VariantField(c1);
                  END;
                ELSIF (ltp = ctp) OR (ctp = intcarptr) AND (ltp = cardptr) THEN
                  IF (c1 < lmin) OR (c2 > lmax) THEN ErrorLS(110) END;
                  VariantField(c1);
                  WHILE c1 < c2 DO
                    INC(c1);
                    VariantField(c1);
                  END;
                ELSE ErrorLS(92); 
                END;
                IF sy = comma THEN GetSy END;
              UNTIL sy = colon; 
            END;
            (*process fields of variant:*)
            GetSy; offse := offset; svtrf := NIL; 
            WHILE (sy = ident) OR (sy = casesy) DO
              FieldList(offse,svtrf); 
            END;
            IF symmod THEN offse := val; GetSy END;
            WHILE cxv <> NIL DO (* enter size of variant in variantlabels *) 
                                (* cxv is set by procedure EnterVariant *)
                                (* field subtagp links variantlabels *)
              WITH cxv^ DO
                size := offse; cxv := subtagp; subtagp := svtrf;
              END;
            END;
            IF offse > maxoffset THEN maxoffset := offse END; 
          END (*while sy = ofsy*);
          IF sy = elsesy THEN (*else variant*)
            GetSy; offse := offset; svtrf := NIL; 
            EnterVariant(tagref^.elsevarp,0);
            WHILE (sy=ident)OR(sy=casesy) DO FieldList(offse,svtrf) END;
            IF symmod THEN offse := val; GetSy END;
            WITH cxv^ DO size := offse; subtagp := svtrf END; 
            IF offse > maxoffset THEN maxoffset := offse END; 
          END;
          tagref^.size := maxoffset; offs := maxoffset; 
          GetSy;
        ELSE (*sy <> casesy*) 
          xh := NIL; 
          WHILE sy <> colon DO
            NEW(x,fields); 
            InitId(x,fields);
            IF symmod THEN GetSy; x^.fldaddr := val;
            ELSE
              IF xh = NIL THEN xh := x ELSE xt^.nxtidp := x END;
              xt := x;
            END;
            EnterList(frf,x); GetSy; 
          END;
          GetSy; ActualTyp(ttp);
          IF symmod THEN
            WITH x^ DO
              idtyp := ttp;
            END;
          ELSE IdentComplete(xh)
          END;
          offs := offset;
        END;
        vtabref := tagref;
      END FieldList;

    BEGIN (*RecordTyp*) 
      offset := 0;
      frf := NIL; vrf := NIL;
      WHILE sy <> endsy DO FieldList(offset,vrf) END; 
      GetSy;
      IF symmod THEN offset := val; GetSy
      END; 
      NEW(lsp,records,fixedpart); 
      WITH lsp^ DO
        size := offset;
        stidp := NIL; inlist := FALSE;
        form := records; rpart := fixedpart;
        fieldp := frf; tagp := vrf; 
      END;
      trf := lsp; 
    END RecordTyp;

    PROCEDURE ArrayTyp(VAR trf: Stptr); 
      VAR lsp, lsp1: Stptr;
          lmin, lmax: CARDINAL; 
    BEGIN (* ArrayTyp *)
      SimpleTyp(lsp); 
      RangeTypeAndBounds(lsp,lsp1,lmin,lmax); (* dummy value for lsp1 *)
      IF sy <> ofsy THEN ArrayTyp(lsp1);
      ELSE GetSy; ActualTyp(lsp1);
      END;
      trf := ArrayStruct(lmin,lmax,lsp,lsp1);
    END ArrayTyp; 

    PROCEDURE SetTyp(VAR trf: Stptr);
      VAR lsp: Stptr;
          lmin, lmax: CARDINAL;
    BEGIN (* SetTyp *)
      SimpleTyp(lsp);
      RangeTypeAndBounds(lsp,trf,lmin,lmax); (* dummy value for trf *)
      IF (lmax > 15) OR (lmin >lmax) THEN ErrorLS(107) END;
      NEW(trf,sets);
      WITH trf^ DO
        size := oneword; stidp := NIL; inlist := FALSE;
        form := sets; basep := lsp;
      END;
    END SetTyp;

    PROCEDURE ProcedureTyp(VAR trf: Stptr);
      VAR dummysize : CARDINAL;
    BEGIN
      ParamList(FALSE,dummysize,trf);
    END ProcedureTyp; 

    PROCEDURE HiddenTyp(VAR trf: Stptr);
    BEGIN
      NEW(trf,hides);
      WITH trf^ DO
        size := oneword; form := hides;
        stidp := NIL; inlist := FALSE;
      END;
    END HiddenTyp;

    PROCEDURE ActualTyp(VAR trf: Stptr);
    BEGIN 
      IF sy = arraysy THEN GetSy; ArrayTyp(trf);
      ELSIF sy = recordsy THEN GetSy; RecordTyp(trf); 
      ELSIF sy = setsy THEN GetSy; SetTyp(trf); 
      ELSIF sy = pointersy THEN GetSy; PointerTyp(trf); 
      ELSIF sy = proceduresy THEN GetSy; ProcedureTyp(trf); 
      ELSIF sy = hidden THEN  GetSy; HiddenTyp(trf);
      ELSE SimpleTyp(trf) END;
    END ActualTyp;

    PROCEDURE FormalTyp(VAR trf: Stptr); 
      VAR lsp,elementp: Stptr; 
    BEGIN 
      IF sy = arraysy THEN GetSy; 
        SimpleTyp(elementp);
        NEW(lsp,arrays); 
        WITH lsp^ DO
          size := doubleword; stidp := NIL; inlist := FALSE;
          form := arrays; dyn := TRUE; 
          ixp := cardptr; elp := elementp; 
        END;
        trf := lsp; 
      ELSE
        SimpleTyp(trf); (* expect type identifier *)
      END;
    END FormalTyp;

  END TypeDefinition; 

  PROCEDURE Module(mp: Idptr; priority: CARDINAL;
                   VAR alladdr: CARDINAL; VAR varp: Idptr);
    VAR initindex : Initrange;
        priotp : Stptr;
        prioval : Constval;

    PROCEDURE ExportList; 
      VAR rf,x: Idptr;
          qualif : BOOLEAN;
    BEGIN
      qualif := sy = qualifiedsy;
      rf := mp^.expp;
      IF qualif OR (sy = exportsy) THEN GetSy;
        WHILE sy = ident DO 
          IF symmod THEN Locate(rf,x);
          ELSE x := NIL;
          END;
          IF x = NIL THEN
            NEW(x,unknown); 
            InitId(x,unknown);
            EnterList(rf,x);
            IF NOT qualif THEN
              (* check whether this identifier is *)
              (* already known in the environment *)
              SearchInBlock(x); (* new value for x *)
              IF (x <> NIL) AND (x^.klass <> unknown) THEN Error(75) END; 
            END;
          END;
          GetSy;
        END 
      END;
      mp^.expp := rf;
      mp^.qualexp := mp^.qualexp OR qualif;
      (* generate inverse link for unknown elements in export-list *) 
      x := mp;
      WHILE rf <> NIL DO
        IF rf^.klass = unknown THEN rf^.nxtidp := x END;
        x := rf;
        rf := x^.link;
      END;
    END ExportList; 
  
    PROCEDURE TestExport; 
      VAR ip : Idptr; 
    BEGIN 
      ip := mp^.expp; 
      WHILE ip <> NIL DO
        IF ip^.klass = unknown THEN ErrorLS(101) END; 
        ip := ip^.link
      END 
    END TestExport; 

    PROCEDURE EnterExport(ip: Idptr); 
      VAR lip : Idptr;
    BEGIN (* enter exportlist of module in mslist of environment *) 
      IF NOT ip^.qualexp THEN
        ip := ip^.expp;
        MsEntry(ip);
        WHILE ip <> NIL DO 
          lip := ip;
          IF lip^.klass = indrct THEN lip := lip^.nxtidp END;
          WITH lip^ DO
            IF klass = mods THEN EnterExport(lip);
            ELSIF (klass = types) AND (idtyp <> NIL) THEN 
              WITH idtyp^ DO
                IF form = enums THEN MsEntry(fcstp) END;
              END;
            END;
          END;
          ip := ip^.link;
        END;
      END;
    END EnterExport; 

    PROCEDURE ImportList;
      (* analyse import list of a module *)
      VAR ip,ep : Idptr;  
          frommod : BOOLEAN;
    BEGIN
      NewImpList(mp^.impp);
      WHILE (sy = importsy) OR (sy = fromsy) DO
        frommod := sy = fromsy;
        IF frommod THEN
          GetSy;
          SearchId(ip);
          IF (ip = NIL) OR (ip^.klass <> mods) THEN (* skip this list *)
            PutSy(fromsy);
            WHILE sy = ident DO PutGetSy END;
          ELSE
            ep := ip^.expp;
            GetSy; 
          END; 
        ELSE PutGetSy; (* importsy *)
        END;
        WHILE sy = ident DO (* identifier skipped if module not found *)
          IF frommod THEN ExportSearch(ep,ip) ELSE SearchId(ip) END;
          IF (ip = NIL) OR (ip^.klass = unknown) THEN
            IF frommod THEN Error(71); GetSy ELSE PutGetSy END;
          ELSE
            EnterImpList(ip);
            GetSy;
          END;
        END; (* while *)
      END; (* while *)
      TermImpList(mp^.impp);
    END ImportList;

    PROCEDURE Block(VAR alladdr: CARDINAL; VAR varp: Idptr;
                    moduleblock: BOOLEAN);

      PROCEDURE DeleteOld(VAR ip: Idptr);
        (* delete old entry of implemented identifier *)
        VAR lip: Idptr;
            pp1,pp2 : Idptr;
      BEGIN (* assume ip <> NIL *)
        IF ip = oldlist THEN oldlist := ip^.link;   
        ELSE  
          lip := oldlist; 
          WHILE lip^.link <> ip DO lip := lip^.link END;
          lip^.link := ip^.link; 
        END; 
        IF oldlist = NIL THEN impl := FALSE END;
        CASE ip^.klass OF 
          types: DISPOSE(ip,types); 
         |pures,funcs: (* delete also parameter and structure entry *) 
            WITH ip^ DO 
              pp1 := idtyp^.fstparam; 
              WHILE pp1 <> NIL DO  
                pp2 := pp1; 
                pp1 := pp2^.vlink;
                DISPOSE(pp2,vars); 
              END;
              IF klass = pures THEN DISPOSE(idtyp,proctypes,pures) 
              ELSE DISPOSE(idtyp,proctypes,funcs) 
              END; 
            END; 
            DISPOSE(ip,pures,FALSE,pures); 
        END; (* case *)   
      END DeleteOld;

      PROCEDURE ConstDeclaration; 
        VAR lip: Idptr;
      BEGIN 
        WHILE sy = ident DO 
          IF symmod THEN SymModSearch(lip) ELSE lip := NIL END;
          IF lip = NIL THEN
            NEW(lip,consts);
            InitId(lip,consts);
            EnterId(lip); 
            GetSy;
            WITH lip^ DO ConstantVal(idtyp,cvalue) END;
          ELSE GetSy; SkipConstant;
          END;
        END;
      END ConstDeclaration; 

      PROCEDURE TypDeclaration; 
        VAR lip: Idptr;
            trf: Stptr; 
            oldp : Idptr;
      BEGIN 
        WHILE sy = ident DO 
          IF symmod THEN SymModSearch(lip) ELSE lip := NIL END;
          IF lip = NIL THEN
            oldp := NIL;
            IF impl AND (nestlevel = 0) AND GlobalKnown(spix) THEN
              (* implementation possible *)
              Locate(oldlist,oldp);
            END;
            NEW(lip,types); 
            InitId(lip,types);
            EnterId(lip); 
            GetSy; ActualTyp(trf);
            IF (trf <> NIL) AND (trf^.stidp = NIL) THEN
              trf^.stidp := lip;
            END;
            lip^.idtyp := trf; 
            IF (oldp <> NIL) AND (oldp^.klass = types) THEN
              (* implementation of hidden type *)
              WITH oldp^.idtyp^ DO (* replace hidden structure *)
                form := opens;
                openstruc := trf;
              END;
              IF NOT FAmong(trf,Stset{ints,cards,words,pointers,
                                      sets,hides}) THEN
                ErrorLS(82)
              END;
              DeleteOld(oldp);
            END;
            Reference(lip);
          ELSE GetSy; SkipType;
          END;
        END;
      END TypDeclaration; 

      PROCEDURE VarDeclaration(VAR vhead: Idptr);
        VAR v, vn, vt : Idptr;
            trf : Stptr;
            space : CARDINAL; (* space for allocation *)
            decl : BOOLEAN; (* identifier is new declared *)
            indac : BOOLEAN; (* indirect access to variable *)
            absval : Constval;
      BEGIN      
        IF vhead = NIL THEN vt := NIL
        ELSE (* search last entry *)
          vn := vhead;
          WHILE vn <> NIL DO vt := vn; vn := vn^.vlink END;
        END;
        WHILE sy = ident DO
          vn := vt; (* mark for new declared list of variables *)
          WHILE sy <> colon DO
            IF symmod THEN SymModSearch(v) ELSE v := NIL END;
            IF v = NIL THEN
              decl := TRUE;
              NEW(v,vars);
              InitId(v,vars);
              WITH v^ DO
                indaccess := FALSE;
                vkind := noparam;
                vaddr := maxcard;
                IF nestlevel <= levmax THEN vlevel := nestlevel;
                ELSE vlevel := levmax;
                END;
                IF vlevel = 0 THEN state := global;
                ELSE state := local;
                END;
                vlink := NIL;
              END;
              IF vhead = NIL THEN vhead := v ELSE vt^.vlink := v END;
              vt := v;
              EnterId(v);
            ELSE decl := FALSE
            END;
            GetSy;
            IF symmod THEN
              IF sy = lbrack THEN
                GetSy; (* lbrack *)
                IF decl THEN
                  WITH v^ DO
                    vaddr := val; state := absolute; vlevel := 0;
                  END;
                END;
                GetSy; (* cardcon *)
                GetSy; (* rbrack *)
              ELSE
                IF decl THEN
                  WITH v^ DO
                    vaddr := val; state := separate; vlevel := 0;
                  END;
                END;
                GetSy; (* cardcon *)
              END;
            ELSIF sy = lbrack THEN
              GetSy; (* lbrack *)
              ConstantVal(trf,absval);
              IF decl THEN
                WITH v^ DO
                  IF FAmong(trf,Stset{cards}) THEN
                    vaddr := absval.value;
                  ELSE ErrorLS(78); vaddr := 0;
                  END;
                  state := absolute;
                  vlevel := 0;
                END;
              END;
              GetSy; (* rbrack *)
            END;
          END; (* WHILE *)
          GetSy; (* colon *)
          IF decl THEN
            ActualTyp(trf);
            space := oneword; indac := FALSE;
            IF trf <> NIL THEN
              IF FAmong(trf,Stset{arrays,records}) THEN indac := TRUE
              ELSE space := trf^.size; (* especially for reals *)
              END;
            END;
            (* allocation and type entry *)
            IF vn = NIL THEN vn := vhead ELSE vn := vn^.vlink END;
            WHILE vn <> NIL DO
              WITH vn^ DO
                idtyp := trf;
                IF (state = local) OR (state = global) THEN
                  vaddr := alladdr; INC(alladdr,space)
                END;
                IF state <> absolute THEN indaccess := indac END;
                Reference(vn);
                vn := vlink;
              END;
            END; 
          ELSE SkipType;
          END;
        END;
      END VarDeclaration;

      PROCEDURE ProcFuncDecl;
        VAR localaddr : CARDINAL;
            localvar : Idptr; (* list of local variables *)
            xb,oldp : Idptr;

        PROCEDURE CompProc(oproc,nproc: Stptr);
          (* compare old procedure from definition module with *)
          (* new declared procedure in implementation module   *)
          VAR op,np : Idptr; (* parameters *) 
              os,ns : Stptr; (* structures *) 
              comp : BOOLEAN; 
   
          PROCEDURE Equivalent(os,ns: Stptr): BOOLEAN;  
          BEGIN 
            RETURN
              (os = ns) OR
              (os<>NIL) AND (os^.form=opens) AND (os^.openstruc=ns);
          END Equivalent; 
  
          PROCEDURE DynArr(sp: Stptr): BOOLEAN; 
          BEGIN 
            RETURN (sp <> NIL) AND (sp^.form = arrays) AND sp^.dyn;
          END DynArr; 

        BEGIN (* CompProc *)
          comp := oproc^.rkind = nproc^.rkind;
          op := oproc^.fstparam; np := nproc^.fstparam;
          WHILE comp AND (op <> np) DO
            IF (op=NIL) OR (np=NIL) OR (op^.vkind<>np^.vkind) THEN
              comp := FALSE 
            ELSE 
              os := op^.idtyp; ns := np^.idtyp; 
              comp := Equivalent(os,ns) OR
                      DynArr(os) AND DynArr(ns) AND
                      Equivalent(os^.elp,ns^.elp); 
              op := op^.vlink; 
              np := np^.vlink; 
            END; 
          END; 
          IF comp AND (oproc^.rkind = funcs) THEN 
            comp := Equivalent(oproc^.funcp,nproc^.funcp) 
          END; 
          IF NOT comp THEN ErrorLS(83) END;
        END CompProc; 

      BEGIN (* ProcFuncDecl *)
        IF symmod THEN SymModSearch(xb) ELSE xb := NIL END;
        IF xb = NIL THEN
          oldp := NIL;
          IF impl AND (nestlevel = 0) AND GlobalKnown(spix) THEN
            (* implementation possible *)
            Locate(oldlist,oldp);
          END;
          localaddr := 0; localvar := NIL;
          NEW(xb,pures,FALSE,pures); (* = NEW(xb,funcs,FALSE,funcs) *)
          InitId(xb,pures);
          EnterId(xb); GetSy;
          IF nestlevel = levmax THEN ErrorLS(77) END;
          INC(nestlevel);
          WITH xb^ DO
            locp := NIL;
            msp := NIL;
            IF nestlevel <= levmax THEN plev := nestlevel;
            ELSE plev := levmax;
            END;
            isstandard := FALSE; (* initialisation *)
            IF symmod THEN procnum := val; GetSy; GetSy; (* symbolic *)
            ELSIF oldp <> NIL THEN procnum := oldp^.procnum; (* impl *)
            ELSE procnum := proccount; INC(proccount);
            END;
            priolev := priority;
            externalaccess := (oldp <> NIL) AND oldp^.externalaccess;
            codeproc := FALSE; (* initialisation *)
          END;
          Reference(xb);
          MarkScope(xb);
          ParamList(NOT symmod,localaddr,xb^.idtyp);
          WITH xb^ DO
            idtyp^.stidp := xb; (* enter identifier reference *)
            klass := idtyp^.rkind;
          END;
          IF (oldp <> NIL) AND (oldp^.klass IN Idset{pures,funcs}) THEN
            (* implementation of procedure from definition module *)
            CompProc(oldp^.idtyp,xb^.idtyp);
            DeleteOld(oldp);
          END;
          IF NOT (symmod OR defmod) THEN (* block expected *)
            PutSy(proceduresy); PutWord(xb);
            Block(localaddr,localvar,FALSE); 
          END;
          ReleaseScope(xb);
          WITH xb^ DO
            varlength := localaddr;
            locvarp := localvar;
          END;
          EndReference(xb);
          DEC(nestlevel);
        ELSE
          GetSy; (* ident *)
          GetSy; (* cardcon = Procedure number *)
          SkipType;
        END;
      END ProcFuncDecl;

    BEGIN (* Block *) 
      MarkInitBlock;
      IF sy = codesy THEN
        (* skip code sequence *)
        IF moduleblock THEN
          Error(112);
          WHILE sy <> endblock DO GetSy END;
        ELSE
          WHILE sy <> endblock DO PutGetSy END;
        END;
      ELSE
        REPEAT
          IF sy = varsy THEN GetSy; VarDeclaration(varp); 
          ELSIF sy = proceduresy THEN GetSy; ProcFuncDecl;
          ELSIF sy = modulesy THEN
            GetSy; ModuleDeclaration(priority,alladdr,varp);
          ELSIF sy = typesy THEN GetSy; TypDeclaration; 
          ELSIF sy = constsy THEN GetSy; ConstDeclaration; 
          END 
        UNTIL (sy = beginsy) OR (sy = endblock) OR (sy = codesy);
        IF sy = codesy THEN
          (* error message in pass1 *)
          (* skip code sequence *)
          WHILE sy <> endblock DO GetSy END;
        ELSIF (sy = beginsy) OR MustInit() THEN
          IF moduleblock THEN
            ToInitModule(initindex);
          END; 
          IF sy = beginsy THEN PutGetSy ELSE PutSy(beginsy) END;
          InitModules;
          (* skip statements *)
          WHILE sy <> endblock DO PutGetSy END; 
          IF moduleblock THEN PutSy(endblock) END;
        END;
      END;
      PutGetSy; (* endblock *)
      ReleaseInitBlock;
    END Block;

  BEGIN (* Module *)   
    PutSy(modulesy); PutWord(mp); 
    IF sy = lbrack THEN (* priority specified *)   
      GetSy; (* lbrack *)
      ConstantVal(priotp,prioval);
      IF (priotp = intcarptr) AND (prioval.value <= maxprio) AND
         ((priority = noprio) OR (priority <= prioval.value))
      THEN
        priority := prioval.value;
      ELSE
        ErrorLS(80);
      END;
      GetSy; (* rbrack *)
    END;
    EnterInitModule(mp,initindex);
    mp^.priolev := priority;
    ImportList;   
    ExportList; 
    MarkScope(mp);
    Block(alladdr,varp,TRUE); 
    TestExport; 
    ReleaseScope(mp);
    EnterExport(mp); 
  END Module; 

  PROCEDURE EnterMods(VAR ip: Idptr);
    (* initialisation and entry of a module *)
  BEGIN
    InitId(ip,mods);
    WITH ip^ DO
      isstandard := FALSE;
      procnum := proccount; INC(proccount);
      IF nestlevel < levmax THEN plev := nestlevel + 1;
      ELSE
        IF nestlevel = levmax THEN ErrorLS(77) END;
        plev := levmax;
      END;
      varlength := procmarkspace; (* for module initialisation *)
      priolev := noprio;
      externalaccess := FALSE;
      locp := NIL; msp := NIL; impp := NIL; expp := NIL;
      qualexp := FALSE; globalmodule := FALSE;
    END; 
    EnterId(ip);
  END EnterMods;
 
  PROCEDURE ModuleDeclaration(oldprio : CARDINAL;
                              VAR alladdr: CARDINAL; VAR varp: Idptr);
    (* declaration of local modules *)
    VAR ip : Idptr;
  BEGIN  
    NEW(ip,mods,FALSE,mods,FALSE);
    EnterMods(ip);
    GetSy; (* identifier *)
    Reference(ip);
    Module(ip,oldprio,alladdr,varp);
    EndReference(ip);
  END ModuleDeclaration;

  PROCEDURE StartDecl; 

    VAR globaladdr : CARDINAL;
        ip : Idptr;
        modcount : CARDINAL;
        modkey : Keyarr;
        ix : CARDINAL;

    PROCEDURE InitImplementation(VAR listp: Idptr; exp: BOOLEAN);
      (* initialisation of an implementation module *)   
      VAR ip1, ip2 : Idptr;
          ndp : Idptr; (* identifier to be new declared *)
          newdecl : BOOLEAN; 

    BEGIN   
      ip1 := listp; ip2 := NIL; 
      WHILE ip1 <> NIL DO 
        newdecl := FALSE; 
        WITH ip1^ DO 
          CASE klass OF 
            types: (* hidden declared types must be implemented *)
              newdecl := (idtyp^.form = hides) AND (idtyp^.stidp = ip1);
              Reference(ip1);
           |vars: (* search for maximal used allocation address *)  
              Reference(ip1);
              IF state <> absolute THEN
                state := global;
                IF vaddr >= globaladdr THEN
                  globaladdr := vaddr;
                  IF indaccess THEN INC(globaladdr,oneword);
                  ELSE INC(globaladdr,idtyp^.size);
                  END;
                END;  
              END;  
           |pures,funcs: (* implementation; maximal procedure number *)
              newdecl := TRUE; 
              IF procnum >= proccount THEN proccount := procnum + 1 END; 
              externalaccess := exp;
          ELSE (* nothing for consts *)
          END; (* case *)     
        END; (* with *)   
        IF newdecl THEN 
          ndp := ip1;  
          IF exp THEN (* replace by unknown identifier in exportlist *) 
            NEW(ip1,unknown); 
            WITH ip1^ DO 
              name := ndp^.name; klass := unknown;
              link := ndp^.link; (* nxtidp is set in procedure ExportList *)
              globmodp := mainmodp;
            END; (* with *) 
            IF ip2 = NIL THEN listp := ip1 ELSE ip2^.link := ip1 END; 
          ELSE (* delete in local list *)  
            IF ip2=NIL THEN listp := ip1^.link;
            ELSE ip2^.link := ip1^.link;
            END;  
            ip1 := ip2; 
          END; 
          (* enter identifier for implementation in separate list *)
          EnterList(oldlist,ndp);                                          
        END;
        ip2 := ip1;
        IF ip1 = NIL THEN ip1 := listp ELSE ip1 := ip1^.link END;
      END; (* while *)   
    END InitImplementation;

    PROCEDURE EnterGlobMods(VAR ip: Idptr);
      (* complete global module entry *)
      VAR ch : CHAR;
          pos : CARDINAL;
    BEGIN
      INC(modcount);
      WITH ip^ DO
        globalmodule := TRUE;
        externalaccess := TRUE; (* call always from environment *)
        modulekey := modkey;
        globvarp := NIL;
        modnum := modcount;
        (* copy identifier *)
        AsciiSetPos(name);
        pos := 0;
        AsciiRead(ch);
        WHILE (ch <> ' ') AND (pos < modnamlength) DO
          identifier[pos] := ch;
          INC(pos);
          AsciiRead(ch);
        END;
        (* fill with 0C *)
        WHILE pos < modnamlength DO
          identifier[pos] := 0C;
          INC(pos);
        END;
      END; 
    END EnterGlobMods;
 
  BEGIN (* StartDecl *)
    nestlevel := 0;
    modcount := 0; (* initialisation *)
    root^.locp := sysmodp; (* enter link to system module *)
    spix := sysmodp^.name;
    EnterId(sysmodp); (* module SYSTEM *)
    GetSy;
    WHILE sy <> eop DO
      ip := NIL;
      impl := FALSE;
      globaladdr := 3; (* 0, 1 and 2 reserved for compiler (pass4) *)
      proccount := 0; (* 0 for initialisation part of global module *)
      symmod := sy = symbolsy;
      defmod := sy = definitionsy;
      impl := sy = implementationsy;
      IF NOT (defmod OR symmod) THEN InitRef END;
      GetSy;
      IF impl THEN (* implementation module *)
        SymModSearch(ip);
        oldlist := NIL;
        IF ip = NIL THEN
          Error(81);
          FOR ix := 0 TO 2 DO modkey[ix] := 0 END;
        ELSE
          mainmodp := ip;
          Reference(ip);
          proccount := 1; (* at least module procedure is entered *)
          InitImplementation(ip^.expp,TRUE);
          InitImplementation(ip^.locp,FALSE);
        END;
        impl := oldlist <> NIL; (* objects to implement *)
      ELSIF symmod THEN (* symbolic module *)
        (* key to compilation version *)
        FOR ix := 0 TO 2 DO modkey[ix] := val; GetSy END;
        SymModSearch(ip);
        IF ip <> NIL THEN
          mainmodp := ip;
          FOR ix := 0 TO 2 DO
            IF modkey[ix] <> ip^.modulekey[ix] THEN Error(86) END;
          END;
        END;   
      ELSE (* defmod or module *)
        GetModuleKey(modkey);
        IF defmod THEN DefModStatus END;
      END;
      IF ip = NIL THEN (* generate new entry *)
        NEW(ip,mods,FALSE,mods,TRUE);
        mainmodp := ip;
        EnterMods(ip);
        EnterGlobMods(ip);
        Reference(ip); (* no effect for defmod or symmod *)
      END;
      GetSy; (* ident *)
      IF defmod OR symmod THEN StopOutput END;
      ResetModuleInit;
      Module(ip,noprio,globaladdr,ip^.globvarp);
      IF defmod OR symmod THEN
        RestartOutput;
      ELSE
        IF impl THEN ErrorLS(84) END; (* some implementations missing *)
        EndReference(ip);
        TermRef;
      END;
    END;
    globvarnext := globaladdr;
    procnumber := proccount;
  END StartDecl; 

BEGIN (* MCPass2 *)
  StartDecl; 
  TermInOut;
END MCPass2.
