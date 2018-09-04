(****************************************
*                                       *
*     MODULA-2 Multi-Pass Compiler      *
*     ****************************      *
*                                       *
*     Implementation for Lilith         *
*                                       *
*                                       *
*     MCPass3:                          *
*                                       * 
*     Pass 3                            *
*     Body analysis                     *
*                                       * 
*     Version C18 of 10.02.82           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

MODULE MCPass3;    (* LG *)

  (* $T-,R- *)

  FROM MCBase IMPORT
    Idptr, Stptr, Idclass, Idset, Structform, Stset,
    Constval, Symbol, intptr, intcarptr, noprio;
  FROM MCP3IO IMPORT
    sy, nptr, PutSy, Error, ErrorLS,
    GetSy, PutGetSy, TermInOut;
  FROM MCP3Ident IMPORT
    FAmong,
    NewImpList, TermImpList, EnterImpList, DisposeImpList,
    SearchId, ExportSearch,
    MarkModScope, ReleaseModScope,
    MarkProcScope, ReleaseProcScope,
    MarkWithScope, ReleaseWithScope, FieldIndex,
    BodyMark, BodyScopes;
  FROM SYSTEM IMPORT TSIZE;
  FROM Storage IMPORT ALLOCATE, DEALLOCATE;
  IMPORT Storage, MCBase, MCP3IO, MCP3Ident, MCOperations;

  PROCEDURE QualIdent(klset: Idset; errnum: CARDINAL; VAR ip: Idptr);
    (* Search a possibly qualified identifier of indicated *)
    (* class. If the search fails then write the error     *)
    (* message ernum. The name spix is taken from MCP3IO.  *)
  BEGIN
    SearchId(ip);
    GetSy; (* next symbol already read *)
    IF ip = NIL THEN ErrorLS(errnum);
    ELSE
      LOOP
        IF ip^.klass <> mods THEN
          IF NOT (ip^.klass IN klset) THEN
            ErrorLS(103); (* identifier not of expected klass *)
            ip := NIL;
          END;
          EXIT;
        ELSIF sy <> period THEN Error(53); ip := NIL; EXIT;
        END;
        GetSy;
        ExportSearch(ip^.expp,ip); (* new value for ip *)
        GetSy; (* next symbol already read *)
        IF ip = NIL THEN ErrorLS(158); EXIT END;
      END; (* LOOP *)
    END;
    IF ip = NIL THEN (* read all qualifications *)
      WHILE sy = period DO GetSy; GetSy END;
    END;
  END QualIdent;

  CONST scalars = Stset{enums,bools,chars,ints,cards,subranges};
        oneword = 1;     (* space used for allocation *)
        doubleword = 2 * oneword;
        maxint = 77777B;   (* maximal integer value *)
        maxcard = 177777B; (* maximal cardinal value *)

  MODULE ExpressionSystem;

    FROM Storage IMPORT ALLOCATE, DEALLOCATE;
    FROM MCBase IMPORT
      noprio,
      Idptr, Stptr, Idclass, Idset,
      Structform, Stset, Varkind, Kindvar,
      charptr, boolptr, intptr, intcarptr,
      realptr, cardptr, wordptr, bitsetptr,
      addrptr, processptr, procptr, strptrs, substptr,
      stringcount, stringroot, Stringptr,
      Stpures, Stfuncs, Symbol, Constval;
    FROM MCP3IO IMPORT
      sy, val, length, spix,
      PutSy, PutWord,
      Savepos, InitSave, ResetSave, ReleaseSave,
      Error, ErrorLS, GetSy, PutGetSy;
    FROM MCP3Ident IMPORT
      Locate, FAmong, SearchId, FieldIndex;
    FROM MCOperations IMPORT RelOp, AddOp, MulOp, NotOp;
    IMPORT
      scalars, oneword, doubleword, maxint, maxcard,
      QualIdent, MCBase;

    EXPORT
      Expression, TypeExpression, ExprSequence,
      ParamCheck, StProcCheck,
      ExprComp, AssignComp, AddressComp,
      Selector, PreSelector, Attribut, Attributmode,
      ConstantRange, ConstantVal, PutConst, InitAt;

    TYPE Attributmode = (constm, varm, exprm);
         Attribut = RECORD
                      mode : Attributmode;
                      atp : Stptr;
                      aval : Constval;
                    END;

    VAR stringtail : Stringptr;

    MODULE TypeHandling;

      FROM MCBase IMPORT
        Idptr, Stptr, Idclass, Structform,
        Stset, Varkind,
        charptr, intptr, cardptr, intcarptr, addrptr;
      IMPORT Attribut, Attributmode, FAmong;

      EXPORT
        ExprComp, AssignComp, AddressComp, WordComp,
        OpenTest, IsString;

      PROCEDURE OpenTest(VAR sp: Stptr);
        (* test on open structure and change to actual structure *)
      BEGIN
        IF (sp<>NIL) AND (sp^.form=opens) THEN
          sp := sp^.openstruc;
        END
      END OpenTest;

      PROCEDURE IsString(s: Stptr): BOOLEAN;
        VAR str: BOOLEAN; 
      BEGIN (* string structure ecpected *)
        str := FALSE;
        IF s<>NIL THEN
          WITH s^ DO
            IF (form=arrays) AND NOT dyn THEN 
              str := (elp=charptr) AND (ixp^.scalp=cardptr)
                                   AND (ixp^.min=0)
            END 
          END (* WITH s^ *)
        END;
        RETURN str;
      END IsString;

      PROCEDURE ProcedureCheck(sp1,sp2: Stptr): BOOLEAN;
        (* check type equality between two procedure structures *)
        VAR p1,p2 : Idptr;
            s1,s2 : Stptr;

        PROCEDURE DynArr(sp: Stptr): BOOLEAN; 
        BEGIN
          RETURN (sp <> NIL) AND (sp^.form = arrays) AND sp^.dyn
        END DynArr;

      BEGIN
        IF sp1^.rkind <> sp2^.rkind THEN RETURN FALSE END;
        p1 := sp1^.fstparam; p2 := sp2^.fstparam;
        LOOP
          IF p1 = p2 THEN EXIT END; (* paramlist checked *)
          IF (p1 = NIL) OR (p2 = NIL) OR (p1^.vkind <> p2^.vkind) THEN
            RETURN FALSE
          ELSE s1 := p1^.idtyp; s2 := p2^.idtyp;
            OpenTest(s1); OpenTest(s2);
            IF s1 <> s2 THEN
              IF DynArr(s1) AND DynArr(s2) THEN
                IF s1^.elp <> s2^.elp THEN RETURN FALSE END;
              ELSE RETURN FALSE
              END;
            END;
          END;
          p1 := p1^.vlink;
          p2 := p2^.vlink;
        END; (* LOOP *)
        (* exit loop only with equality *)
        IF sp1^.rkind = funcs THEN RETURN sp1^.funcp = sp2^.funcp 
        ELSE RETURN TRUE
        END;
      END ProcedureCheck; 

      PROCEDURE ExprComp(at1,at2 : Attribut) : BOOLEAN;
        (* compare two types to compatibility *)
        VAR t1p,t2p : Stptr;
      BEGIN
        t1p := at1.atp;
        t2p := at2.atp;
        IF (t1p=t2p) OR (t1p=NIL) OR (t2p=NIL) THEN RETURN TRUE END;
        IF t1p^.form = subranges THEN t1p := t1p^.scalp END;
        IF t2p^.form = subranges THEN t2p := t2p^.scalp END;
        IF (t1p=t2p) OR (t1p=NIL) OR (t2p=NIL) THEN RETURN TRUE END;
        IF (t2p = intcarptr) AND
           ((t1p = intptr) OR (t1p = cardptr)) THEN RETURN TRUE END;
        IF (t1p = intcarptr) AND
           ((t2p = intptr) OR (t2p = cardptr)) THEN RETURN TRUE END;
        IF ((at1.mode=varm) <> (at2.mode=varm)) THEN
          (* compatibility of different structrecs only between *)
          (* (constants/procedures) AND (variables/fields)      *)
          IF (t1p^.form=pointers) AND (t2p^.form=pointers) THEN
            RETURN TRUE (* NIL compatible to each pointer *)
          ELSIF (t1p^.form=proctypes) AND (t2p^.form=proctypes) THEN
            RETURN ProcedureCheck(t1p,t2p)
          ELSIF IsString(t1p) AND IsString(t2p) THEN (* string compatibility *)
            RETURN ((at1.mode=varm) <> (t1p^.ixp^.max<t2p^.ixp^.max)) OR
                   (t1p^.ixp^.max = t2p^.ixp^.max) OR
                   (t1p^.size = 0) OR (t2p^.size = 0);
          END;
        END;
        RETURN FALSE;
      END ExprComp;

      PROCEDURE AssignComp(at1,at2: Attribut): BOOLEAN;
        (* assignment compatibility *)
        CONST incar = Stset{ints,cards};
      BEGIN
        RETURN ExprComp(at1,at2) OR
               FAmong(at1.atp,incar) AND FAmong(at2.atp,incar)
      END AssignComp;

      PROCEDURE AddressComp(at1,at2: Attribut): BOOLEAN;
        (* compatibility to type ADDRESS *)
        VAR sp : Stptr;
      BEGIN
        IF at1.atp = addrptr THEN sp := at2.atp
        ELSIF at2.atp = addrptr THEN sp := at1.atp
        ELSE sp := NIL
        END;
        RETURN FAmong(sp,Stset{pointers})
      END AddressComp;

      PROCEDURE WordComp(sp: Stptr): BOOLEAN;
        (* compatibility to formal WORD parameter *)
      BEGIN
        RETURN NOT FAmong(sp,Stset{arrays,records,reals});
      END WordComp;

    END TypeHandling;

    PROCEDURE InitAt(VAR at : Attribut);
    BEGIN
      WITH at DO
        mode := varm;
        atp := NIL;
        aval.value := 0;
      END;
    END InitAt; 

    PROCEDURE StringStruct(length: CARDINAL): Stptr;
      (* get string structure entry *)
      VAR sp : Stptr;
    BEGIN
      IF (length > 20) OR (strptrs[length] = NIL) THEN
        (* generate new entry *)
        NEW(sp,arrays);
        WITH sp^ DO
          size := (length + 1) DIV 2; (* packing *)
          stidp := NIL;
          form := arrays; dyn := FALSE;
          elp := charptr;
          NEW(ixp,subranges);
          WITH ixp^ DO
            size := oneword;
            stidp := NIL;
            form := subranges;
            scalp := cardptr;
            min := 0; max := length - 1;
          END;
        END;
        IF length <= 20 THEN strptrs[length] := sp END;
      ELSE
        sp := strptrs[length];
      END;
      RETURN sp;
    END StringStruct;

    PROCEDURE AllocString(strval: Stringptr; length: CARDINAL);
    BEGIN
      IF strval^.loadoffset = maxcard THEN
        strval^.loadoffset := stringcount;
        INC(stringcount,(length + 2) DIV 2);
        (* one or two characters 0C terminate the constant *)
        (* enter link *)
        IF stringroot = NIL THEN stringroot := strval;
        ELSE stringtail^.slink := strval;
        END;
        stringtail := strval;
      END;
    END AllocString;

    PROCEDURE PutConst(sp: Stptr; cval: Constval);
    BEGIN
      PutSy(anycon);
      PutWord(sp); 
      PutWord(cval.value);
      IF IsString(sp) THEN
        AllocString(cval.svalue,sp^.ixp^.max + 1);
      END;
    END PutConst;

    PROCEDURE TypeExpression(VAR at : Attribut; forms: Stset);
      (* expression with type in forms expected *)
    BEGIN Expression(at); 
      IF NOT FAmong(at.atp,forms) THEN ErrorLS(121) END;
    END TypeExpression;

    PROCEDURE VariableStandard(VAR at: Attribut; forms: Stset);
      (* variable with type in forms expected *)
    BEGIN Expression(at); 
      IF at.mode = varm THEN
        IF NOT FAmong(at.atp,forms) THEN ErrorLS(121) END
      ELSE ErrorLS(122)
      END;
    END VariableStandard;

    PROCEDURE VariantAnalyse(tagref: Stptr; VAR sz: Constval);
      (* analyse of procedure parameters for record variants *)
      (* in standard procedures NEW, DISPOSE, TSIZE *)
      VAR equal : BOOLEAN;
          vxv,vtrf : Stptr;
          ttyp : Stptr; 
          tval : Constval;
    BEGIN
      vtrf := tagref;
      WHILE vtrf <> NIL DO
        IF sy = rparent THEN vtrf := NIL;
        ELSE GetSy; (* tags are not written in the il1 file *)
          ConstantVal(ttyp,tval); 
          WITH vtrf^ DO 
            IF (ttyp = tagtyp) OR 
               ((ttyp = intcarptr) AND FAmong(tagtyp,Stset{ints,cards})) OR
               ((tagtyp^.form = subranges) AND (ttyp = tagtyp^.scalp)) THEN
              vxv := fstvarp; equal := FALSE;
              WHILE (vxv <> NIL) AND NOT equal DO
                WITH vxv^ DO
                  IF varval = tval.value THEN equal := TRUE 
                  ELSE vxv := nxtvarp
                  END
                END; (* WITH vxv^ *)
              END;
              IF NOT equal AND (elsevarp <> NIL) THEN (* ELSE variant *)
                vxv := elsevarp; equal := TRUE;
              END;
              IF equal THEN sz.value := vxv^.size;
                vtrf := vxv^.subtagp;
                IF (vtrf = NIL) AND (sy <> rparent) THEN Error(132) END
              ELSE Error(148);
                vtrf := NIL;
              END;
            ELSE Error(92);
              vtrf := NIL;
            END;
          END;
        END;
      END;
      WHILE sy <> rparent DO GetSy; ConstantVal(ttyp,tval) END; 
    END VariantAnalyse; 

    PROCEDURE StProcCheck(ip: Idptr);
      VAR ok : BOOLEAN;
          i : CARDINAL; 
          at,at1 : Attribut;
          ltp : Stptr;
          lval : Constval;
          nam : Stpures;
          subp : Idptr;
    BEGIN
      nam := ip^.pname;
      (* test on procedures to be sustituted *)
      subp := substptr;
      WHILE (subp <> NIL) AND (subp^.pname <> nam) DO
        subp := subp^.link;
      END;
      IF subp <> NIL THEN (* procedure must be substituted *)
        spix := subp^.name; (* ATTENTION : spix is changed *)
        SearchId(ip);
        IF (ip <> NIL) AND (ip^.klass IN Idset{pures,vars}) THEN
          (* procedure found for substitution *)
          (* initialisation of attributes for compatibility check *)
          at.atp := subp^.idtyp; at.mode := exprm;
          at1.atp := ip^.idtyp; at1.mode := varm;
          IF NOT ExprComp(at,at1) THEN ErrorLS(125) END;
        ELSE ErrorLS(124);
        END;
      END;
      PutSy(namesy); PutWord(ip);
      PutGetSy; (* lparent *)
      i := 0;
      CASE nam OF
        incp,decp: (*INC,DEC*)
          IF sy = rparent THEN Error(127);
          ELSE
            VariableStandard(at,scalars);
            IF sy <> rparent THEN PutGetSy;
              TypeExpression(at1,Stset{ints,cards});
            END; 
          END;
       |disp,newp:  (* NEW,DISPOSE *)
          IF sy = rparent THEN
            Error(127); ltp := NIL;
          ELSE
            VariableStandard(at,Stset{pointers});
            ltp := at.atp;
          END;
          IF FAmong(ltp,Stset{pointers}) THEN
            ltp := ltp^.elemp
          END;
          IF ltp = NIL THEN lval.value := 0 
          ELSE
            WITH ltp^ DO
              lval.value := size; 
              IF form = records THEN
                VariantAnalyse(tagp,lval);
              END;
            END; (* WITH ltp^ *)
          END;
          PutSy(comma);
          PutConst(cardptr,lval);
          (* substituted procedures now with two        *)
          (* parameters on the il1-file: (pointer,size) *)
       |inlp,exlp:  (* INCL,EXCL *) 
          IF sy = rparent THEN Error(127);
          ELSE
            VariableStandard(at,Stset{sets});
            IF sy = rparent THEN Error(127);
            ELSE PutGetSy; TypeExpression(at1,scalars);
              IF FAmong(at.atp,Stset{sets}) THEN
                at.atp := at.atp^.basep;
                IF NOT AssignComp(at,at1) THEN ErrorLS(128) END;
              END;
            END;
          END;
       |nprp:  (* NEWPROCESS *)
          LOOP
            IF sy = comma THEN PutGetSy END;
            IF sy = rparent THEN Error(127); EXIT END;
            INC(i);
            CASE i OF
              1: Expression(at);
                 at1.atp := procptr; at1.mode := varm;
                 IF NOT ExprComp(at,at1) THEN ErrorLS(127) END;
             |2,3: TypeExpression(at,Stset{cards});
             |4: Expression(at);
                 WITH at DO
                   IF NOT ((mode = varm) AND (atp = processptr)) THEN
                     ErrorLS(127)
                   END
                 END;
                 EXIT;
             END (* CASE *)
           END; 
       |trsp:  (* TRANSFER *)
          LOOP
            IF sy = comma THEN PutGetSy END;
            IF sy = rparent THEN Error(127); EXIT END;
            INC(i);
            Expression(at);
            WITH at DO
              IF NOT ((mode = varm) AND (atp = processptr)) THEN
                ErrorLS(127)
              END
            END;
            IF i = 2 THEN EXIT END;
          END;
       |halp:  (* HALT *) (* NO ACTIVITY *)
      END; (* CASE *)
      IF sy = rparent THEN PutGetSy;
      ELSE ErrorLS(127); ExprSequence;
      END;
    END StProcCheck; 

    PROCEDURE TypFunction(VAR at : Attribut); 
      CONST forms = Stset{sets,pointers} + scalars;
      VAR lat : Attribut;
    BEGIN
      PutGetSy; (* lparent *)
      IF sy = rparent THEN Error(137);
      ELSE
        Expression(lat);
        IF (at.atp <> NIL) AND (lat.atp <> NIL) THEN
          IF (at.atp^.size = lat.atp^.size) THEN
            IF (lat.mode = constm) AND
               FAmong(at.atp,forms) AND FAmong(lat.atp,forms)
            THEN
              at.mode := constm;
              at.aval := lat.aval;
            ELSIF (lat.atp^.form = arrays) AND (lat.atp^.dyn) THEN
              ErrorLS(120);
            END;
          ELSE
            at.atp := NIL;
            ErrorLS(120);
          END;
        END;
      END;
      IF sy = rparent THEN
        PutGetSy;
      ELSE
        ErrorLS(127); ExprSequence;
      END;
    END TypFunction;

    PROCEDURE PreSelector(x: Idptr; VAR at: Attribut);
    BEGIN
      WITH x^ DO
        OpenTest(idtyp);
        WITH at DO
          IF klass IN Idset{vars,fields} THEN mode := varm;
          ELSE mode := exprm;
          END;
          atp := idtyp;
          IF NOT (klass IN Idset{consts,types}) THEN
            IF klass = fields THEN
              PutSy(field); PutWord(FieldIndex()); PutSy(period);
            END;
            PutSy(namesy); PutWord(x);
          END;
        END (* WITH at *)
      END (* WITH x^ *)
    END PreSelector;

    PROCEDURE Selector(VAR at : Attribut);
      VAR lat,indat : Attribut;
          x : Idptr;
    BEGIN
      REPEAT
        IF sy = lbrack THEN PutGetSy;
          Expression(lat);
          WITH at DO
            IF atp <> NIL THEN
              WITH atp^ DO
                IF form = arrays THEN
                  OpenTest(ixp); OpenTest(elp);
                  indat.atp := ixp; indat.mode := varm; 
                  IF NOT AssignComp(indat,lat) THEN ErrorLS(128) END;
                  atp := elp
                ELSE ErrorLS(130)
                END;
              END; (* WITH atp^ *)
            END;
          END; (* WITH at *)
          PutGetSy; (* rbrack *)
        ELSIF sy = period THEN
          PutGetSy;
          WITH at DO
            IF atp <> NIL THEN
              WITH atp^ DO
                IF form <> records THEN Error(131)
                ELSE
                  Locate(fieldp,x); (* entries with klass = fields assumed *)
                  IF x <> NIL THEN
                    PutSy(namesy); PutWord(x);
                    OpenTest(x^.idtyp);
                    atp := x^.idtyp;
                  ELSE Error(73)
                  END;
                END
              END; (* WITH atp^ *)
            END;
          END; (* WITH at *)
          GetSy;
        ELSIF sy = arrow THEN
          WITH at DO
            IF atp = addrptr THEN atp := wordptr
            ELSIF atp <> NIL THEN
              WITH atp^ DO
                IF form <> pointers THEN Error(146)
                ELSE
                  OpenTest(elemp);
                  atp := elemp
                END
              END; (* WITH typptr^ *)
            END;
          END; (* WITH at *)
          PutGetSy;
        END;
      UNTIL (sy <> lbrack) AND (sy <> period) AND (sy <> arrow);
    END Selector;

    PROCEDURE ParamCheck(fstp : Idptr);
      VAR at1,at2 : Attribut;
          ls :Idptr;
          comp : BOOLEAN;

      PROCEDURE DynArrCheck(dynarelp,aptr: Stptr);
        (* compare element types *) 
      BEGIN
        IF dynarelp <> wordptr THEN
          IF aptr^.form = arrays THEN
            IF aptr^.elp <> dynarelp THEN
              ErrorLS(135)
            END;
          ELSE ErrorLS(128);
          END;
        END;
      END DynArrCheck;

    BEGIN (* ParamCheck *)
      ls := fstp;
      WHILE sy <> rparent DO
        Expression(at1);
        IF ls = NIL THEN Error(132) 
        ELSE
          WITH at1 DO
            IF atp <> NIL THEN
              WITH ls^ DO 
                IF (vkind = varparam) AND (mode <> varm) THEN
                  ErrorLS(134);
                END;
                OpenTest(idtyp);
                IF (idtyp<>NIL) AND (idtyp^.form=arrays) AND
                   idtyp^.dyn THEN
                  DynArrCheck(idtyp^.elp,atp)
                ELSIF idtyp = wordptr THEN
                  IF NOT WordComp(atp) THEN ErrorLS(150) END; 
                ELSE
                  at2.atp := idtyp; at2.mode := varm;
                  IF vkind=varparam THEN comp := ExprComp(at2,at1)
                  ELSE comp := AssignComp(at2,at1)
                  END;
                  IF NOT (comp OR AddressComp(at1,at2)) THEN
                    ErrorLS(128)
                  END
                END;
              END; (* WITH ls^ *)
            END;
            ls := ls^.vlink;
          END; (* WITH at1 *)
        END;
        IF sy = comma THEN PutGetSy END;
      END; (* WHILE *)
      PutGetSy; 
      IF ls <> NIL THEN ErrorLS(137) END;
    END ParamCheck;

    PROCEDURE ExprSequence;
      (* Terminate a sequence of Expressions *)
      VAR at: Attribut;
    BEGIN
      WHILE sy <> rparent DO
        IF sy = comma THEN PutGetSy END;
        Expression(at);
      END;
      PutGetSy; (* rparent *)
    END ExprSequence;

    PROCEDURE Expression(VAR at : Attribut);
      VAR lat : Attribut;
          tpat,tplat : Stptr;
          op : Symbol;
          forms: Stset;
          err : BOOLEAN;
          save : Savepos;

      PROCEDURE SimpleExpression(VAR at : Attribut);
        VAR lat : Attribut;
            op : Symbol;
            sign : BOOLEAN;
            save : Savepos;

        PROCEDURE Term(VAR at : Attribut);
          VAR lat : Attribut;
              op : Symbol;
              save : Savepos;
 
          PROCEDURE Factor(VAR at : Attribut);
            VAR x : Idptr;
                lat : Attribut;
                save : Savepos;
                mustreset : BOOLEAN;

            PROCEDURE SetConstructor(VAR at: Attribut);
              VAR styp, ctyp : Stptr;
                  smin, smax, v1, v2 : CARDINAL;
                  c1, c2 : Constval;
                  spat : BITSET; (* set pattern *)

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
              smin := 0; smax := 15; spat := {};
              IF FAmong(at.atp,Stset{sets}) THEN 
                styp := at.atp^.basep;
              ELSE ErrorLS(99);
                styp := NIL;
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
                  v1 := c1.value; v2 := c2.value;
                  IF (v1 < smin) OR (v2 > smax) OR (ctyp = intptr) THEN ErrorLS(98);
                  ELSE
                    spat := spat + RangeSet(v1,v2);
                  END;
                ELSE ErrorLS(97); 
                END;
                IF sy = comma THEN GetSy END;
              END; (* WHILE *)
              GetSy;
              at.mode := constm;
              at.aval.value := CARDINAL(spat);
            END SetConstructor;

            PROCEDURE SkipFactor;
              (* skip semantical incorrect elements of factor *)
              VAR at : Attribut;
            BEGIN
              InitAt(at);           
              IF sy = lconbr THEN SetConstructor(at)
              ELSE Selector(at);
                IF sy = lparent THEN GetSy; ExprSequence END;
              END;
            END SkipFactor;

            PROCEDURE StFuncCheck(ip: Idptr; VAR at : Attribut);
              CONST all = Stset{enums..records};
              VAR at1 : Attribut; 
                  lval : Constval;
                  sp : Stptr;
                  nam : Stfuncs;

              PROCEDURE NextParameter(VAR at: Attribut; forms: Stset);
              BEGIN
                IF sy = rparent THEN Error(127);
                ELSE TypeExpression(at,forms);
                END;
              END NextParameter;

            BEGIN
              InitAt(at);
              at.mode := exprm;
              nam := ip^.fname;
              PutSy(namesy); PutWord(ip);
              PutGetSy; (* lparent *)
              CASE nam OF
                higf: (* HIGH *)
                  at.atp := cardptr;
                  IF sy = rparent THEN Error(127);
                  ELSE
                    VariableStandard(at1,Stset{arrays});
                    WITH at1 DO
                      IF (atp<>NIL) AND (atp^.form=arrays) THEN
                        IF NOT atp^.dyn THEN
                          at.mode := constm;
                          at.aval.value := atp^.ixp^.max;
                          IF at.aval.value<=maxint THEN
                            at.atp := intcarptr;
                          END;
                        END;
                      END;
                    END;
                  END;
               |sizf: (* SIZE *)
                  at.atp := intcarptr;
                  IF sy = rparent THEN Error(127);
                  ELSE
                    VariableStandard(at1,all); 
                    WITH at1 DO
                      IF atp <> NIL THEN
                        IF NOT ((atp^.form=arrays) AND atp^.dyn) THEN
                          at.mode := constm;
                          at.aval.value := atp^.size;
                          IF at.aval.value > maxint THEN
                            at.atp := cardptr;
                          END;
                        END;
                      END;
                    END;
                  END;
               |tszf: (* TSIZE *)
                  at.atp := intcarptr;
                  IF sy = ident THEN
                    QualIdent(Idset{types},129,ip);
                    (* new value for ip *)
                    IF ip <> NIL THEN
                      sp := ip^.idtyp;
                      IF sp = NIL THEN lval.value := 0;
                      ELSE
                        WITH sp^ DO
                          lval.value := size;
                          IF form = records THEN
                            VariantAnalyse(tagp,lval)
                          END;
                        END;
                      END;
                      at.mode := constm;
                      at.aval := lval;
                    END;
                  ELSE Error(135);
                  END;
                  CASE sy OF
                    lparent, lconbr, lbrack, period, arrow:
                      Error(135);
                      SkipFactor;
                  ELSE (* nothing *)
                  END; (* CASE *)
               |adrf: (* ADR *)
                  at.atp := addrptr;
                  IF sy = rparent THEN Error(127);
                  ELSE VariableStandard(at1,all); 
                  END;
               |oddf: (* ODD *)
                  at.atp := boolptr;
                  NextParameter(at1,Stset{ints,cards});
               |absf: (* ABS *)
                  InitAt(at1);
                  NextParameter(at1,Stset{ints,cards,reals});
                  at.atp := at1.atp;
               |capf: (* CAP *)
                  at.atp := charptr;
                  NextParameter(at1,Stset{chars});
               |fltf: (* FLOAT *)
                  at.atp := realptr;
                  NextParameter(at1,Stset{ints,cards});
               |trcf: (* TRUNC *)
                  at.atp := cardptr;
                  NextParameter(at1,Stset{reals});
               |ordf: (* ORD *)
                  at.atp := cardptr;
                  NextParameter(at1,scalars);
               |chrf: (* CHR *)
                  at.atp := charptr;
                  NextParameter(at1,Stset{ints,cards});
               |valf: (* VAL *)
                  at.atp := NIL;
                  IF sy = ident THEN
                    QualIdent(Idset{types},129,ip); (* new value for ip *)
                    IF ip <> NIL THEN
                      IF FAmong(ip^.idtyp,scalars) THEN
                        at.atp := ip^.idtyp;
                      ELSE ErrorLS(121);
                      END;
                    END;
                    PutSy(namesy); PutWord(ip);
                  ELSE Error(135);
                  END;
                  CASE sy OF
                    lparent, lconbr, lbrack, period, arrow:
                      Error(135);
                      SkipFactor;
                  ELSE (* nothing *)
                  END; (* CASE *)
                  IF sy = comma THEN PutGetSy END;
                  NextParameter(at1,Stset{ints,cards});
              END; (* CASE nam *) 
              IF sy = rparent THEN PutGetSy;
              ELSE ErrorLS(127); ExprSequence;
              END;
            END StFuncCheck;

          BEGIN (* Factor *)
            InitSave(save);
            mustreset := TRUE;
            InitAt(at);
            IF sy = ident THEN
              QualIdent(Idset{consts..funcs},73,x);
              IF x <> NIL THEN (* ident IN [consts..funcs] *)
                IF (x^.klass IN Idset{pures,funcs}) AND
                   x^.isstandard
                THEN
                  IF sy = lparent THEN
                    IF x^.klass = funcs THEN StFuncCheck(x,at);
                    ELSE
                      Error(145);
                      PutGetSy; (* lparent *)
                      ExprSequence;
                    END;
                  ELSE
                    CASE sy OF
                      lconbr, lbrack, period, arrow:
                        Error(144); SkipFactor;
                    ELSE
                      ErrorLS(147);
                    END; (* CASE *)
                  END;
                ELSE
                  PreSelector(x,at);
                  WITH x^ DO
                    CASE klass OF
                      consts :
                        CASE sy OF
                          lparent, lconbr, lbrack, period, arrow:
                            Error(123); InitAt(at);
                            SkipFactor;
                        ELSE
                          at.mode := constm;
                          IF idtyp = realptr THEN (* make a copy of the real value *)
                            NEW(at.aval.rvalue);
                            at.aval.rvalue^ := cvalue.rvalue^;
                          ELSE at.aval := cvalue;
                          END;
                          mustreset := FALSE;
                        END; (* CASE *)
                     |types :
                        CASE sy OF
                          lconbr: SetConstructor(at); mustreset := FALSE;
                         |lparent:
                            PutSy(namesy); PutWord(x);
                            TypFunction(at);
                         |lbrack, period, arrow:
                            Error(144); InitAt(at);
                            SkipFactor;
                        ELSE
                          ErrorLS(137); InitAt(at);
                        END; (* CASE *)
                     |vars,fields,pures,funcs:
                        IF at.mode = varm THEN Selector(at) END;
                        CASE sy OF
                          lparent:
                            at.mode := exprm;
                            IF (klass=funcs)AND(priolev<>noprio) THEN
                              externalaccess := TRUE;
                            END;
                            PutGetSy;
                            IF at.atp <> NIL THEN
                              WITH at.atp^ DO
                                IF (form=proctypes) AND (rkind=funcs) THEN
                                  ParamCheck(fstparam);
                                  at.atp := funcp;
                                ELSE ErrorLS(145);
                                  at.atp := NIL;
                                  ExprSequence;
                                END;
                              END;
                            ELSE ExprSequence;
                            END;
                         |lconbr, lbrack, period, arrow:
                            Error(144); InitAt(at);
                            SkipFactor;
                        ELSE
                          IF (klass = pures) OR (klass = funcs) THEN
                            externalaccess := TRUE;
                            IF plev <> 1 THEN ErrorLS(141) END;
                          END;
                        END; (* CASE *)
                    END; (* CASE *)
                  END; (* WITH x^ *)
                END;
              ELSE (* x = NIL *)
                SkipFactor;
              END;
            ELSIF sy = lconbr THEN (* BITSET *)
              at.atp := bitsetptr; SetConstructor(at);
              mustreset := FALSE;
            ELSIF sy = notsy THEN
              PutGetSy;
              Factor(at);
              IF FAmong(at.atp,Stset{bools}) THEN
                IF at.mode = constm THEN
                  NotOp(at.aval,at.aval);
                ELSE
                  at.mode := exprm;
                END;
              ELSE
                at.mode := exprm;
                ErrorLS(138);
              END;
            ELSIF sy = lparent THEN
              PutGetSy;
              Expression(at);
              IF at.mode = varm THEN at.mode := exprm END;
              PutGetSy
            ELSE (* constants *)
              WITH at DO
                mode := constm;
                aval.value := val;
                CASE sy OF
                  intcon : atp := intptr;
                 |intcarcon : atp := intcarptr;
                 |cardcon : atp := cardptr;
                 |charcon : atp := charptr;
                 |realcon : atp := realptr;
                 |stringcon : atp := StringStruct(length);
                END; (* CASE *)
                mustreset := FALSE;
                GetSy;
              END;
            END;
            IF at.mode = constm THEN
              IF mustreset THEN ResetSave(save) END;
              PutConst(at.atp,at.aval);
            END;
            ReleaseSave(save);
          END Factor;

        BEGIN (* Term *)
          InitSave(save);                      
          Factor(at);
          WHILE (sy >= andsy) AND (sy <= modsy) DO
            op := sy;
            PutGetSy;
            Factor(lat);
            IF at.atp = NIL THEN at.atp := lat.atp;
            ELSE
              IF (at.atp=intcarptr) AND
                 FAmong(lat.atp,Stset{ints,cards}) THEN
                at.atp := lat.atp;
              END;
              IF ExprComp(at,lat) THEN
                CASE op OF
                  andsy: forms := Stset{bools}
                 |times: forms := Stset{ints,cards,sets,reals}
                 |slash: forms := Stset{sets,reals}
                 |divsy,modsy: forms := Stset{ints,cards}
                END; (* CASE *)
                IF FAmong(at.atp,forms) THEN
                  IF (at.mode = constm) AND (lat.mode = constm) THEN
                    MulOp(at.aval,lat.aval,at.aval,op,at.atp,err);
                    IF err THEN
                      at.mode := exprm;
                      IF NOT FAmong(at.atp,Stset{reals}) THEN
                        ErrorLS(94);
                      END;
                    ELSE
                      ResetSave(save);
                      PutConst(at.atp,at.aval);
                    END;
                  ELSE at.mode := exprm;
                  END;
                ELSE
                  at.mode := exprm; 
                  ErrorLS(140);
                END;
              ELSE
                at.mode := exprm;
                ErrorLS(143);
              END;
            END;
          END; (* WHILE *) 
          ReleaseSave(save);
        END Term;

      BEGIN (* SimpleExpression *)
        InitSave(save);
        sign := (sy = minus) OR (sy = plus);
        IF sign THEN
          op := sy;
          IF op = minus THEN PutGetSy ELSE GetSy END;
        END;
        Term(at);
        IF sign THEN
          WITH at DO
            IF mode = varm THEN mode := exprm END;
            IF (atp = intcarptr) OR FAmong(atp,Stset{ints,reals}) THEN
              IF op = minus THEN
                IF mode = constm THEN
                  IF atp = realptr THEN lat.aval.rvalue := NIL;
                  ELSE lat.aval.value := 0;
                  END;
                  AddOp(lat.aval,aval,aval,op,atp,err);
                  IF err THEN
                    mode := exprm;
                    ErrorLS(94);
                  ELSE
                    ResetSave(save);
                    PutConst(atp,aval);
                  END;
                END;
              END;
            ELSIF FAmong(atp,Stset{cards}) THEN
              IF op = minus THEN mode := exprm; ErrorLS(121) END;
            ELSE
              mode := exprm;
              ErrorLS(121); 
            END;
          END; (* WITH *)
        END;
        WHILE (sy >= plus) AND (sy <= orsy) DO
          op := sy;
          PutGetSy;
          Term(lat);
          IF at.atp = NIL THEN at.atp := lat.atp;
          ELSE
            IF (at.atp = intcarptr) AND
               FAmong(lat.atp,Stset{ints,cards}) THEN
              at.atp := lat.atp;
            END;
            IF ExprComp(at,lat) THEN
              CASE op OF
                orsy: forms := Stset{bools}
               |plus,minus: forms := Stset{ints,cards,sets,reals}
              END; (* CASE *)
              IF FAmong(at.atp,forms) THEN
                IF (at.mode = constm) AND (lat.mode = constm) THEN
                  AddOp(at.aval,lat.aval,at.aval,op,at.atp,err);
                  IF err THEN
                    at.mode := exprm;
                    IF NOT FAmong(at.atp,Stset{reals}) THEN
                      ErrorLS(94);
                    END;
                  ELSE
                    ResetSave(save);
                    PutConst(at.atp,at.aval);
                  END;
                ELSE at.mode := exprm;
                END;
              ELSE
                at.mode := exprm;
                ErrorLS(140);
              END;
            ELSE
              at.mode := exprm;
              ErrorLS(143);
            END;
          END;
        END; (* WHILE *)
        ReleaseSave(save);
      END SimpleExpression;

    BEGIN (* Expression *)
      InitSave(save);
      SimpleExpression(at);
      IF (sy >= eql) AND (sy <= insy) THEN
        op := sy;
        PutGetSy;
        SimpleExpression(lat);
        tpat := at.atp;
        tplat := lat.atp;
        IF op = insy THEN 
          IF FAmong(tplat,Stset{sets}) THEN 
            lat.atp := tplat^.basep;
            IF ExprComp(at,lat) THEN
              IF (at.mode=constm) AND (lat.mode=constm) THEN
                RelOp(at.aval,lat.aval,at.aval,insy,tpat,err);
                IF err THEN
                  at.mode := exprm;
                  ErrorLS(94);
                ELSE
                  ResetSave(save);
                  PutConst(boolptr,at.aval);
                END;
              ELSE 
                at.mode := exprm;
              END;
            ELSE
              at.mode := exprm;
              ErrorLS(142);
            END;
          ELSE
            at.mode := exprm;
            ErrorLS(149);
          END
        ELSIF ExprComp(at,lat) OR AddressComp(at,lat) THEN
          IF tpat = intcarptr THEN tpat := tplat END;
          CASE op OF
            eql,neq : forms := Stset{sets,pointers,reals} + scalars
           |geq,leq : forms := Stset{sets,reals} + scalars
           |grt,lss : forms := Stset{reals} + scalars
          END;
          IF FAmong(tpat,forms) THEN
            IF (at.mode=constm) AND (lat.mode=constm) THEN
              RelOp(at.aval,lat.aval,at.aval,op,tpat,err);
              IF err THEN
                at.mode := exprm;
                IF NOT FAmong(tpat,Stset{reals}) THEN
                  ErrorLS(94);
                END;
              ELSE
                ResetSave(save);
                PutConst(boolptr,at.aval);
              END;
            ELSE at.mode := exprm;
            END;
          ELSE
            at.mode := exprm;
            ErrorLS(140);
          END;
        ELSE
          at.mode := exprm;
          ErrorLS(143);
        END;
        at.atp := boolptr;
      END;
      ReleaseSave(save);
    END Expression;

    PROCEDURE Constant(VAR at: Attribut);
      VAR save : Savepos;
    BEGIN
      InitSave(save);
      Expression(at);
      WITH at DO
        IF mode = constm THEN
          ResetSave(save);
          IF ((atp=cardptr)OR(atp=intptr))AND(aval.value<=maxint) THEN
            atp := intcarptr; 
          END;
        ELSE ErrorLS(136);
        END;
      END;
      ReleaseSave(save);
    END Constant;

    PROCEDURE ConstantRange(VAR tp: Stptr; VAR c1, c2: Constval);
      VAR fval,lval : CARDINAL;
          at : Attribut;
    BEGIN
      Constant(at);
      tp := at.atp;
      fval := at.aval.value; lval := fval;
      IF sy = range THEN
        IF FAmong(tp,scalars) THEN 
          GetSy; (* range *)
          Constant(at);
          WITH at DO
            IF tp = intcarptr THEN
              IF FAmong(atp,Stset{ints,cards}) THEN tp := atp END;
            ELSIF atp = intcarptr THEN
              IF FAmong(tp,Stset{ints,cards}) THEN atp := tp END;
            END;
            IF tp = atp THEN
              lval := aval.value;
              IF tp = intptr THEN
                IF INTEGER(lval) < INTEGER(fval) THEN
                  ErrorLS(95);
                  lval := fval;
                END;
              ELSIF lval < fval THEN ErrorLS(95); lval := fval;
              END;
            ELSE ErrorLS(95);
            END;
          END; (* WITH *)
        ELSE Error(96); GetSy;
        END;
      END;
      c1.value := fval; c2.value := lval;
    END ConstantRange;

    PROCEDURE ConstantVal(VAR tp: Stptr; VAR c: Constval);
      VAR at : Attribut;
    BEGIN
      Constant(at);
      tp := at.atp;
      c := at.aval;
    END ConstantVal;

  BEGIN
    stringcount := 0;
    stringroot := NIL;
  END ExpressionSystem;

  PROCEDURE ModulDeclaration; 
    VAR mptr : Idptr; 

    PROCEDURE ImportList;
      (* analyse import list of a module *) 
      VAR ip, ep : Idptr; 
          frommod : BOOLEAN; 
    BEGIN 
      NewImpList(mptr^.impp); 
      WHILE (sy = importsy) OR (sy = fromsy) DO 
        frommod := sy = fromsy;
        GetSy; 
        IF frommod THEN 
          SearchId(ip); 
          IF (ip = NIL) OR (ip^.klass <> mods) THEN (* skip this list *) 
            Error(105);
            WHILE sy = ident DO GetSy END; 
          ELSE 
            GetSy;
            ep := ip^.expp; 
          END; 
        END; 
        WHILE sy = ident DO (* identifier skipped if module not found *) 
          IF frommod THEN
            ExportSearch(ep,ip); 
            IF ip = NIL THEN Error(71) END; 
          ELSE
            SearchId(ip); 
            IF ip = NIL THEN Error(73) END;
          END; 
          IF ip <> NIL THEN EnterImpList(ip) END; 
          GetSy; 
        END; (* while *) 
      END; (* while *) 
      TermImpList(mptr^.impp); 
    END ImportList; 

  BEGIN mptr := nptr; 
    GetSy;
    ImportList;
    MarkModScope(mptr);
    Block(mptr);
    ReleaseModScope;
    DisposeImpList(mptr^.impp);
    GetSy; (* endblock *)
  END ModulDeclaration;
 
  PROCEDURE Block(bptr : Idptr);
    VAR inloop : BOOLEAN;
        priority : CARDINAL;

    PROCEDURE BlockDeclaration;
      VAR lnptr: Idptr;

    BEGIN lnptr := nptr;
      PutGetSy;
      MarkProcScope(lnptr);
      Block(lnptr); 
      ReleaseProcScope;
      PutGetSy; (* endblock *)
    END BlockDeclaration;

    PROCEDURE Statement;

      PROCEDURE StatSeq1(s1 : Symbol);
      BEGIN
        WHILE sy <> s1 DO Statement END
      END StatSeq1; 

      PROCEDURE StatSeq2(s1,s2 : Symbol);
      BEGIN
        WHILE (sy <> s1) AND (sy <> s2) DO Statement END
      END StatSeq2; 

      PROCEDURE StatSeq3(s1,s2,s3 : Symbol);
      BEGIN
        WHILE (sy <> s1) AND (sy <> s2) AND (sy <> s3) DO Statement END
      END StatSeq3; 

      PROCEDURE Assignment;
        VAR at1,at2 : Attribut;
            x : Idptr;
      BEGIN
        InitAt(at1);
        QualIdent(Idset{vars,fields},122,x);
        IF x <> NIL THEN
          PreSelector(x,at1); 
          Selector(at1);
          PutGetSy; (* comma *)
          Expression(at2);
          IF NOT (AssignComp(at1,at2) OR AddressComp(at1,at2)) THEN
            ErrorLS(128)
          END;
        ELSE
          Selector(at1);
          PutGetSy; (* comma *)
          Expression(at2);
        END;
      END Assignment;

      PROCEDURE CallStatement;
        VAR x : Idptr;
            ok : BOOLEAN;
            at : Attribut;
            fp : Idptr;

        PROCEDURE SkipCall;
          (* skip semantical incorrect parts of call *)
          VAR at: Attribut;
        BEGIN
          InitAt(at);
          Selector(at);
          PutGetSy; (* lparent *)
          ExprSequence;
        END SkipCall;

      BEGIN
        IF sy = namesy THEN x := nptr; GetSy; (* module bodies *)
        ELSE QualIdent(Idset{vars,fields,pures,funcs},73,x);
        END;
        IF x <> NIL THEN
          IF (x^.klass = pures) AND x^.isstandard THEN
            IF sy = lparent THEN StProcCheck(x);
            ELSE Error(144); SkipCall;
            END;
          ELSIF (x^.klass = funcs) AND x^.isstandard THEN
            IF sy = lparent THEN ErrorLS(157) ELSE Error(144) END;
            SkipCall;
          ELSE
            PreSelector(x,at);
            IF at.mode = varm THEN
              Selector(at);
            ELSE (* pures, funcs, mods *)
              WITH x^ DO
                IF (priolev <> priority) AND (priolev <> noprio) THEN
                  IF (priority = noprio) OR (priority < priolev) THEN
                    externalaccess := TRUE;
                  ELSE
                    ErrorLS(161);
                  END;
                END;
              END;
            END;
            ok := TRUE;
            IF at.atp = NIL THEN fp := NIL; (* may be a module call *)
            ELSE
              WITH at.atp^ DO
                IF (form = proctypes) AND (rkind <> funcs) THEN
                  fp := fstparam;
                ELSE ErrorLS(157); ok := FALSE;
                END;
              END; (* WITH *) 
            END;
            ok := ok AND (sy = lparent);
            IF ok THEN
              PutGetSy; (* lparent *)
              ParamCheck(fp);
            ELSE
              IF sy <> lparent THEN Error(144) END;
              SkipCall;
            END;
          END;
        ELSE (* x = NIL *)
          SkipCall;
        END;
      END CallStatement;

      PROCEDURE IfStatement;
        VAR at : Attribut;
      BEGIN
        LOOP TypeExpression(at,Stset{bools});
          StatSeq3(endsy,elsesy,elsifsy);
          IF sy <> elsifsy THEN EXIT END;
          PutGetSy; 
        END;
        IF sy = elsesy THEN PutGetSy; StatSeq1(endsy) END;
        PutGetSy; (* endsy *) 
      END IfStatement;

      PROCEDURE WithStatement;
        VAR x : Idptr;
            ltp : Stptr;
            at : Attribut;
            isrecord : BOOLEAN;
      BEGIN
        QualIdent(Idset{vars,fields},122,x);
        IF x <> NIL THEN PreSelector(x,at);
          Selector(at);
        ELSE InitAt(at);
          Selector(at);
        END;
        ltp := at.atp;
        isrecord := FAmong(ltp,Stset{records}); 
        IF isrecord THEN MarkWithScope(ltp^.fieldp);
        ELSE ErrorLS(121);
        END;
        StatSeq1(endsy);
        IF isrecord THEN ReleaseWithScope END;
        PutGetSy;
      END WithStatement;

      PROCEDURE CaseStatement;
        VAR at1,at2 : Attribut;
            c1, c2 : Constval;
      BEGIN
        TypeExpression(at1,scalars);
        WHILE sy = ofsy DO
          PutGetSy; 
          REPEAT
            WITH at2 DO
              mode := constm;
              ConstantRange(atp,c1,c2); 
              IF ExprComp(at1,at2) THEN
                PutConst(atp,c1);
                IF atp = intptr THEN
                  WHILE INTEGER(c1.value) < INTEGER(c2.value) DO
                    IF c1.value = maxcard THEN c1.value := 0 ELSE INC(c1.value) END;
                    PutConst(atp,c1);
                  END;
                ELSE
                  WHILE c1.value < c2.value DO
                    INC(c1.value);
                    PutConst(atp,c1);
                  END;
                END;
              ELSE ErrorLS(128);
              END;
            END;
            IF sy = comma THEN GetSy END;
          UNTIL sy = colon;
          PutGetSy; 
          StatSeq3(ofsy,elsesy,endsy);
        END;
        IF sy = elsesy THEN PutGetSy; StatSeq1(endsy) END;
        PutGetSy; (* endsy *) 
      END CaseStatement;

      PROCEDURE LoopStatement;
        VAR oldinloop : BOOLEAN;
      BEGIN
        oldinloop := inloop;
        inloop := TRUE;
        StatSeq1(endsy);
        PutGetSy;
        inloop := oldinloop;
      END LoopStatement;

      PROCEDURE ExitStatement;
      BEGIN
        IF NOT inloop THEN ErrorLS(151) END;
      END ExitStatement;

      PROCEDURE ReturnStatement;
        VAR at1,at2 : Attribut;
      BEGIN (* expression in parenthesis *)
        CASE bptr^.klass OF
          funcs : (* function block *)
            IF sy <> lparent THEN Error(153)
            ELSE
              PutGetSy; (* lparent *)
              Expression(at1);
              at2.atp := bptr^.idtyp^.funcp;
              at2.mode := varm;
              IF NOT (AssignComp(at2,at1) OR AddressComp(at1,at2)) THEN
                ErrorLS(155)
              END;
              PutGetSy; (* rparent *)
            END;
         |pures, mods : (* procedure or module block *)
            IF sy = lparent THEN Error(154); Expression(at1) END;
        END;
      END ReturnStatement;

      PROCEDURE ForStatement; 
        VAR at1,at2: Attribut;
            ip : Idptr;
            sp : Stptr;
            lval : Constval;
      BEGIN
        QualIdent(Idset{vars},122,ip); (* single identifier expected *)
        IF ip <> NIL THEN
          PreSelector(ip,at1); 
          Selector(at1);
          IF NOT FAmong(at1.atp,scalars) THEN ErrorLS(139) END;
        ELSE
          InitAt(at1); Selector(at1);
        END;
        PutGetSy; (* comma *)
        LOOP
          TypeExpression(at2,scalars);
          IF NOT AssignComp(at1,at2) THEN Error(128) END;
          IF sy = tosy THEN PutGetSy ELSE EXIT END;
        END; (* LOOP *)
        IF sy = bysy THEN
          PutGetSy; 
          ConstantVal(sp,lval);
          PutConst(sp,lval);
          IF NOT FAmong(sp,Stset{ints,cards}) THEN ErrorLS(156) END;
        END;
        StatSeq1(endsy);
        PutGetSy;
      END ForStatement;

      PROCEDURE RepeatStatement;
        VAR at : Attribut;
      BEGIN StatSeq1(untilsy); PutGetSy;
       TypeExpression(at,Stset{bools});
      END RepeatStatement;

      PROCEDURE WhileStatement;
        VAR at : Attribut;
      BEGIN TypeExpression(at,Stset{bools});
        StatSeq1(endsy); PutGetSy;
      END WhileStatement;

      VAR lsy : Symbol; (* leading symbol in statement *)

    BEGIN (* Statement *)
      lsy := sy; PutGetSy;
      CASE lsy OF
        becomes: Assignment;
       |call: CallStatement;
       |ifsy: IfStatement; 
       |withsy: WithStatement
       |casesy: CaseStatement
       |loopsy: LoopStatement
       |whilesy: WhileStatement
       |repeatsy: RepeatStatement
       |forsy: ForStatement
       |returnsy: ReturnStatement
       |exitsy: ExitStatement
      ELSE (* nothing *)
      END;
    END Statement;

    PROCEDURE CodeSequence;

      CONST maxcodebuff = 50;

      TYPE Codebuffer = ARRAY [1..maxcodebuff] OF CARDINAL;
           Codeptr = POINTER TO Codebuffer;

      VAR codes , entry : Codeptr;
          ix : CARDINAL;

      PROCEDURE Code;
        CONST maxcodeval = 377B;
        VAR ctp : Stptr;
            cval : Constval;
      BEGIN
        ConstantVal(ctp,cval);
        IF FAmong(ctp,Stset{ints,cards}) THEN
          IF (ctp = intcarptr) AND (cval.value <= maxcodeval) THEN
            IF ix < maxcodebuff THEN
              INC(ix);
              codes^[ix] := cval.value;
            ELSE
              ErrorLS(159);
            END;
          ELSE
            ErrorLS(160);
          END;
        ELSE
          ErrorLS(156);
        END;
      END Code;

    BEGIN (* CodeSequence *)
      NEW(codes);
      ix := 0;
      WHILE sy <> endblock DO Code END;
      IF bptr^.klass <> mods THEN
        bptr^.codeproc := TRUE;
        bptr^.codelength := ix;
        IF ix > 0 THEN
          ALLOCATE(entry,ix*TSIZE(CARDINAL));
          (* array structure is overlayed for entry *)
          WHILE ix > 0 DO
            entry^[ix] := codes^[ix];
            DEC(ix);
          END;
        ELSE
          entry := NIL;
        END;
        bptr^.codeentry := CARDINAL(entry);
      END;
      DISPOSE(codes);
    END CodeSequence;

  BEGIN (* Block *) 
    IF sy = codesy THEN
      PutGetSy;
      CodeSequence;
    ELSE
      REPEAT
        IF sy = proceduresy THEN BlockDeclaration;
        ELSIF sy = modulesy THEN ModulDeclaration
        END;
      UNTIL (sy = beginsy) OR (sy = endblock);
      inloop := FALSE;
      priority := bptr^.priolev;
      BodyMark;
      IF sy = beginsy THEN PutGetSy;
        WHILE sy <> endblock DO Statement END;
      END;
      (* update space used by procedure on stack *)
      INC(bptr^.varlength,BodyScopes()*oneword);
    END;
  END Block;

  PROCEDURE StartBodyAnalysis;
  BEGIN
    GetSy;
    IF sy = modulesy THEN ModulDeclaration; END;
    PutSy(endblock); (* temporary *)
  END StartBodyAnalysis;

BEGIN (* MCPass3 *)
  StartBodyAnalysis;
  TermInOut;
END MCPass3.
