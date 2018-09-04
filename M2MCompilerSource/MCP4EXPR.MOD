IMPLEMENTATION MODULE MCP4ExpressionSys;  (* Ch. Jacobi  5.4.81 *)

  (* $T-,R- *)

(* expressions 
   for Pass 4 of the Compiler for the Lilith Computer *)

  IMPORT 
    SYSTEM, Storage, MCBase, MCP4Global, MCP4CodeSys, MCMnemonics;

  FROM SYSTEM IMPORT
    ADDRESS;

  FROM MCBase IMPORT  
    Idptr, Stptr, 
    Idclass, Idset, Structform, Stset,
    Varkind, Kindvar, Stpures, Stfuncs,
    boolptr, charptr, intptr, cardptr, wordptr, 
    realptr, addrptr, 
    Symbol;

  FROM MCP4Global IMPORT 
    level,
    loadCount, spPosition, 
    blockNptr, 
    WriteCodeWord, WriteIntermediateWord,
    GetSymbol, sy, val, 
    nptr, cstPtr, cString, controlRangeCheck, 
    Error, CompilerError, Assert;

  FROM MCP4CodeSys IMPORT
   
    (*Codesys*)
         PC, 
         Emit, Emit2, 
         MarkLong,  UpdateLong,
         MarkShort, UpdateShort,
         LinkageMark, 
         PutConstString,  
        
    (*SimpleCode*)
         EmitPacked, EmitLI, EmitLSW, EmitSSW, EmitCL,
         IAddToTop, UConstMul, UConstDiv, UConstMod, 

    (*TypeSystem*)
         IsArrayType, ByteSize, IsSetType;

  FROM MCP4AttributSys IMPORT
    ArithmeticType, AtMode, Attribut,
    HasAlreadyCode,
    TestBaseType, ResultType, Arithmetic,
    RangeCheck, RangeCheckForConstant, SizeType, SimpleType,
    Load, LoadAddr, Store,
    LoadDynHigh, PreAssign;

  FROM MCP4CallSys IMPORT 
    ProcFuncCall;

  FROM MCMnemonics IMPORT                                                   
    LID,  LLW,  SLW,
    FADD, FSUB, FMUL, FDIV, FCMP, FNEG,
    ORJP, ANDJP,
    ADD,  SUB,  MUL,  DIVV, UADD, USUB, UMUL, UDIV, UMOD,
    EQL,  NEQ,  LSS,  LEQ,  GTR,  GEQ,  NEG,
    ORR,  XORR, ANDD, COM,  NOTT, INN,
    ULSS, ULEQ, UGTR, UGEQ,
    CHKZ,
    GB1,  GB,   COPT;

   
  MODULE WithSystem;
    FROM Storage IMPORT
      ALLOCATE, DEALLOCATE;
    IMPORT
      Assert, Attribut, PreAssign, blockNptr,
      AtMode, EmitPacked, LoadAddr, loadCount, HasAlreadyCode,
      LLW, SLW;
    EXPORT 
      EnterWith, ExitWith, UseWith;


    TYPE
      WithPt = POINTER TO WithRecord;   
      WithRecord = 
        RECORD wat: Attribut;
          next: WithPt      
        END;

    VAR 
      firstWith: WithPt;
      withCount: INTEGER;


    PROCEDURE UseWith(i: INTEGER; VAR fat: Attribut);
      (* fat gets the description of the with element.   
         May produce code for loading the address of the with variable *)
      VAR lWith: WithPt; l: INTEGER;
     BEGIN lWith := firstWith;
      Assert(i<=withCount);
      FOR l := 1 TO i DO lWith := lWith^.next END;
      WITH lWith^ DO
        fat := wat
      END;
      IF fat.mode=addrLoadedMod THEN
        EmitPacked(LLW, blockNptr^.varlength-CARDINAL(i));
        INC(loadCount)
      END
    END UseWith; 


    PROCEDURE EnterWith(VAR fat: Attribut); 
      (* Store fat for further use by UseWith,  
         code for entry of a with statement *)
      VAR lWith: WithPt; i: INTEGER;
    BEGIN 
      INC(withCount); lWith := firstWith;
      FOR i := 2 TO withCount DO lWith := lWith^.next END;
      NEW(lWith^.next); lWith := lWith^.next;
      PreAssign(fat);
      IF fat.mode IN HasAlreadyCode THEN
        LoadAddr(fat);
        EmitPacked(SLW, blockNptr^.varlength-CARDINAL(withCount));
        DEC(loadCount)
      END;
      WITH lWith^ DO
        wat := fat
      END
    END EnterWith;
 

    PROCEDURE ExitWith;
      (* Exit the innermost with statement *)
      VAR lWith: WithPt; i: INTEGER;
    BEGIN lWith := firstWith;
      FOR i := 1 TO withCount DO lWith := lWith^.next END;
      DISPOSE(lWith);
       Assert(withCount>0);
      DEC(withCount);
    END ExitWith;
 

  BEGIN 
    withCount := 0;
    NEW(firstWith)
  END WithSystem;


  PROCEDURE Difference(a, b: CARDINAL): CARDINAL;
  BEGIN
    IF a>=b THEN RETURN a-b END;
    RETURN 177777B-b+a+1
  END Difference;


  PROCEDURE Designator(VAR fat : Attribut);   


    PROCEDURE TypFunction(ftp: Stptr; VAR fat : Attribut);   
      (* ftp is type of function *)
    BEGIN GetSymbol; GetSymbol; 
      Expression(fat);  
      IF fat.mode=stringTemplateMod THEN LoadAddr(fat) END;
      WITH fat DO
        IF (typtr^.size<>ftp^.size) 
           OR ((typtr^.form=arrays) AND typtr^.dyn) THEN Error(220) 
        ELSE
          (* in type conversion no rangetests!
             IF ftp=charptr THEN
               Load(fat); EmitLI(377B); Emit(ANDD); DEC(loadCount)
             END;
          *) 
          IF ftp^.size>2 THEN LoadAddr(fat) 
          ELSE Load(fat)
          END
        END;
        typtr := ftp
      END
    END TypFunction;  


    PROCEDURE PreDesignator(VAR fat: Attribut);
      (* The code for loading a procedure base address will already be generated 
         if necessary, but neither the value nor the address is completely
         loaded *)
      VAR i: CARDINAL;
          lType: Stptr;
    BEGIN
      WITH fat DO
        IF sy=namesy THEN
          WITH nptr^ DO
            typtr := idtyp;
            IF klass=vars THEN
              addr := vaddr;
              CASE state OF
                global:   mode := globalMod;
              | local:  i := level-vlevel;
                  IF i=0 THEN mode := localMod
                  ELSE mode := addrLoadedMod; 
                    INC(loadCount);
                    IF i=1 THEN Emit(GB1)  
                    ELSE Emit(GB); Emit(i)
                    END
                  END;
                  IF (typtr^.form=arrays) AND typtr^.dyn THEN
                    dynArrLevelDiff := i; dynArrOffset := vaddr+1;
                  END
              | absolute: mode := absolutMod
              | separate: mode := externalMod; 
                          moduleNo := globmodp^.modnum
              END;
              IF indaccess THEN
                lType := typtr; typtr := intptr;
                Load(fat); mode := addrLoadedMod; addr := 0;
                typtr := lType
              END
            ELSIF (klass=pures) OR (klass=funcs) OR (klass=mods) THEN
              mode := procedureMod;
              procPtr := nptr
            ELSE (*klass=types*)
              Assert(klass=types);
              TypFunction(idtyp, fat)
            END (*IF klass=..*)  
          END (*WITH nptr^*)
        ELSE (*sy=field*)
          Assert(sy=field); 
          UseWith(val, fat)
        END;
      END (*WITH fat*);
      GetSymbol
    END PreDesignator;


    PROCEDURE SwitchAddr(VAR fat: Attribut; x: CARDINAL);
      (* adds x to the address of fat, may generate code *)
    BEGIN
      CASE fat.mode OF       (*prepare fat*)
          externalMod, addrLoadedMod, localMod, globalMod:    
            IF (fat.addr+x) > 255 THEN LoadAddr(fat) END;
            INC(fat.addr, x)
        | indexMod, doubleIndexMod, absolutMod: 
            IF x<>0 THEN
              LoadAddr(fat);
              fat.addr := x
            END
        ELSE CompilerError  
      END;
    END SwitchAddr;


    PROCEDURE IndexVar(VAR fat: Attribut);
      (* compilation of array indexing *)
      VAR iat: Attribut; xtyp: Stptr;
          elsize: CARDINAL;
          isdyn: BOOLEAN;
          newMode: AtMode;
    BEGIN
      WITH fat DO  (* attribut for array *)
        Assert(IsArrayType(typtr));
        LoadAddr(fat); (* -> mode := addrLoadedMod, addr := 0 *)
        WITH typtr^ DO
          xtyp := ixp;
          elsize := elp^.size; isdyn := dyn;
          IF (elsize=1) AND ByteSize(elp) THEN newMode := byteIndexMod 
          ELSIF elsize=2 THEN newMode := doubleIndexMod
          ELSE newMode := indexMod
          END
        END;
        Expression(iat); 
        IF (iat.mode=constantMod) AND NOT isdyn THEN 
          RangeCheckForConstant(xtyp, iat);
          IF (newMode<>byteIndexMod) THEN
            SwitchAddr(fat, Difference(iat.value, xtyp^.min)*elsize)
          ELSE (* for byte indexing no optimization is possible *) 
            Load(iat);
            IF xtyp^.min<>0 THEN 
              EmitLI(xtyp^.min); 
              IF TestBaseType(xtyp)=intptr THEN Emit(SUB)
              ELSE Emit(USUB) END
            END;
            mode := byteIndexMod;
          END
        ELSE 
          Load(iat);
          IF isdyn THEN
            IF controlRangeCheck THEN 
              LoadDynHigh(fat);
              Emit(CHKZ); DEC(loadCount)
            END
          ELSE
            IF xtyp^.min<>0 THEN 
              EmitLI(xtyp^.min); 
              IF TestBaseType(xtyp)=intptr THEN Emit(SUB)
              ELSE Emit(USUB) END
            END;
            IF controlRangeCheck THEN
              EmitLI(Difference(xtyp^.max, xtyp^.min)); 
              Emit(CHKZ); DEC(loadCount)
            END
          END;
          mode := newMode;                     
          IF (mode=indexMod) AND (elsize>1) THEN
            UConstMul(elsize)
          END;
        END; 
        typtr := typtr^.elp
      END
    END IndexVar;

 
  BEGIN (* Designator *)  
    PreDesignator(fat);  
    WHILE (sy=lbrack) OR (sy=arrow) OR (sy=period) DO  
      IF sy = lbrack THEN GetSymbol;  
        IndexVar(fat);
        Assert(sy=rbrack);  
        GetSymbol (*rbrack*)  
      ELSIF sy = arrow THEN (* indirection via a pointer *)
        GetSymbol;  
        Load(fat); 
        WITH fat DO  
          IF typtr=addrptr THEN typtr := wordptr
          ELSE
            Assert((typtr<>NIL) AND (typtr^.form=pointers));  
            typtr := typtr^.elemp  
          END;
          mode := addrLoadedMod; addr := 0
        END  
      ELSE (* record field *)
        GetSymbol; (*period*) 
        Assert((sy=namesy) AND (nptr<>NIL) AND (nptr^.klass=fields));
        SwitchAddr(fat, nptr^.fldaddr); 
        fat.typtr := nptr^.idtyp;
        GetSymbol  
      END  
    END  
  END Designator;  
 

  PROCEDURE Factor(VAR fat: Attribut);   
    VAR rptr: POINTER TO (*REAL*)
                RECORD r1, r2: CARDINAL END;
  BEGIN (* Factor *)  
    IF sy = lparent THEN
      GetSymbol; Expression(fat); GetSymbol; (* rparent *)  
    ELSIF sy = notsy THEN GetSymbol; Factor(fat);         
      IF IsSetType(fat.typtr) THEN           
        Load(fat); Emit(COM)
      ELSE (* BOOLEAN *)
        IF fat.mode<>constantMod THEN
          Load(fat); Emit(NOTT)
        ELSE fat.value := 1-fat.value (* NOT fat.value *)
        END
      END  
    ELSIF (sy = namesy) OR (sy = field) THEN
      Designator(fat);  
      IF sy=lparent THEN (* function call *)  
        GetSymbol; ProcFuncCall(fat)  
      END
    ELSE (*Constant*)   
      Assert(sy=anycon);  
      WITH fat DO 
        typtr := cstPtr;  
        IF NOT SimpleType(fat) THEN                         
          mode := stringTemplateMod;
          addr := cString^.loadoffset;
          PutConstString(cstPtr, cString)
        ELSIF typtr=realptr THEN 
          mode := doubleConstMod; 
          rptr := ADDRESS(cString);
          r1 := rptr^.r1;  r2 := rptr^.r2;
          Load(fat)
        ELSE mode := constantMod;
          value := CARDINAL(val)
        END  
      END; 
      GetSymbol  
    END  
  END Factor;   


  PROCEDURE Term(VAR fat: Attribut);   
    VAR 
      lat: Attribut; opsy: Symbol;  
      AType: ArithmeticType;
      lPC: INTEGER; 

    PROCEDURE Multiplication(VAR fat, lat: Attribut);
      VAR cat: Attribut; opt: BOOLEAN;                     
    BEGIN opt := FALSE;
      IF fat.mode<>constantMod THEN Load(fat) END;        
      GetSymbol;
      Factor(lat);
      IF lat.mode<>constantMod THEN Load(lat) END;
      CASE Arithmetic(fat, lat) OF
        bitwise: 
           Load(fat); Load(lat);  (* commutative !!  *)
                                  (* if lat=loaded and fat=const *)
           Emit(ANDD); DEC(loadCount) |

        floating:
           Load(fat); Load(lat);  (* commutative !! *)
           Emit(FMUL); DEC(loadCount, 2) |

        signed:
           IF fat.mode=constantMod THEN cat := fat; opt := TRUE;
             IF lat.mode<>loadedMod THEN Load(lat) END (* commutative!! *)
           ELSIF lat.mode=constantMod THEN cat := lat; opt := TRUE;
             (* pass 3: fat.mode=loadedMod *)
             Assert(fat.mode=loadedMod) 
           END;
           IF opt THEN
             IF cat.iValue<>1 THEN
               IF cat.iValue=0 THEN Emit(COPT); Emit(XORR)
               ELSIF cat.iValue=2 THEN Emit(COPT); Emit(ADD)
               ELSE EmitLI(cat.value); Emit(MUL); DEC(loadCount)
               END
             END
           ELSE
             Emit(MUL); DEC(loadCount)
           END;
           fat.mode := loadedMod |

        unSigned:
           IF fat.mode=constantMod THEN   
             IF lat.mode<>loadedMod THEN Load(lat) END; (*commutative !!*)
             UConstMul(fat.value);
           ELSIF lat.mode=constantMod THEN
             (* pass 3: fat.mode=loadedMod *)
             Assert(fat.mode=loadedMod); 
             UConstMul(lat.value)
           ELSE
             Emit(UMUL); DEC(loadCount);
           END;
           fat.mode := loadedMod
      END 
    END Multiplication;

  BEGIN (* Term *)  
    lPC := 0;
    Factor(fat);  
    WHILE (sy >= andsy) AND (sy <= modsy) DO opsy := sy;  
      IF sy=times THEN
        Multiplication(fat, lat)
      ELSE
        Load(fat);
        GetSymbol;  
        IF opsy=andsy THEN
          Emit(ANDJP); MarkShort(lPC)
        END;
        Factor(lat); 
        AType := Arithmetic(fat, lat);
        CASE opsy OF
          andsy:
            Load(lat); DEC(loadCount);
            Assert(AType=logical)
            (* Do nothing, short circuit AND *)

        | divsy:
            CASE AType OF
                signed:
                  Load(lat); DEC(loadCount);
                  Emit(DIVV)
              | unSigned:
                  IF lat.mode=constantMod THEN UConstDiv(lat.value)
                  ELSE 
                    Load(lat); DEC(loadCount);
                    Emit(UDIV)
                  END
            END
       
        | slash:
            Load(lat); DEC(loadCount);
            CASE AType OF
                bitwise:  Emit(XORR)
              | floating: Emit(FDIV); DEC(loadCount)
            END;

        | modsy:
            CASE AType OF
                signed: Load(lat); DEC(loadCount);
                        Emit(UMOD) (* no integer modulus *)
              | unSigned:
                  IF lat.mode=constantMod THEN 
                    UConstMod(lat.value)
                  ELSE 
                    Load(lat); DEC(loadCount);
                    Emit(UMOD)
                  END
            END
         
        END
      END;
      fat.typtr := ResultType(fat, lat)
    END;  
    UpdateShort(lPC)
  END Term;  


  PROCEDURE SimpleExpression(VAR fat: Attribut);   
    (* fat describes the first operand and the result *)
    VAR 
      opsy: Symbol;  
      lat: Attribut; (* descriptor of second operand *)
      negb: BOOLEAN; (* a negation has to take place *)  
      AType: ArithmeticType;
      lPC: INTEGER; 
  BEGIN lPC := 0;
    negb := sy = minus; 
    IF negb THEN GetSymbol END;  
    Term(fat);  
    IF negb THEN  
      IF Arithmetic(fat, fat)=floating THEN
        Load(fat); 
        Emit(FNEG) 
      ELSIF fat.mode <> constantMod THEN
        (* negation *)
        Load(fat);
        Emit(NEG)
      ELSE 
        fat.iValue := -fat.iValue  
      END  
    END;  
    WHILE (sy >= plus) AND (sy <= orsy) DO opsy := sy;
      Load(fat);
      GetSymbol;
      IF opsy=orsy THEN
        Emit(ORJP); MarkShort(lPC)
      END;
      Term(lat); Load(lat);
      AType := Arithmetic(fat, lat);
      DEC(loadCount);
      CASE opsy OF   
        minus:
          CASE AType OF
              signed:   Emit(SUB)
            | unSigned: Emit(USUB)
            | bitwise:  Emit(COM); Emit(ANDD)
            | floating: Emit(FSUB); DEC(loadCount)
          END
      | plus:
          CASE AType OF
              signed:   Emit(ADD)
            | unSigned: Emit(UADD)
            | bitwise:  Emit(ORR) (*sets*)
            | floating: Emit(FADD); DEC(loadCount)
          END
      | orsy:        
         (* booleans,   do nothing, short circuit OR *)
      END;  
      fat.typtr := ResultType(fat, lat)
    END;  
    UpdateShort(lPC)
  END SimpleExpression;   


  PROCEDURE Expression(VAR fat: Attribut);          
    (* fat describes the first operand and the result *)
    VAR 
      inst: CARDINAL;  
      opsy : Symbol;
      lat: Attribut; (* descriptor of second operand *)  

    PROCEDURE EmitCompare(i: CARDINAL; t: ArithmeticType);
      (* Generate code for compare  
         compare instructions must have the same order   
         for signed and unSigned arithmetic *)
    BEGIN
      IF t=unSigned THEN
        IF i>NEQ THEN i := i+ULSS-LSS END;
      ELSIF t=floating THEN Emit(FCMP)
      END;
      Emit(i)
    END EmitCompare;

  BEGIN (* Expression *)
    SimpleExpression(fat);
    IF sy=insy THEN GetSymbol;  
      Load(fat);
      SimpleExpression(lat); Load(lat); 
      Emit(INN); DEC(loadCount);
      WITH fat DO
        (*mode := loadedMod;*)
        typtr := boolptr
      END  
    ELSIF (sy >= eql) AND (sy <= leq) THEN
      opsy := sy;  
      Load(fat);
      IF (fat.typtr^.form=sets) AND (opsy=geq) THEN Emit(COM) END;
      GetSymbol; SimpleExpression(lat); Load(lat);
      DEC(loadCount);
      IF (fat.typtr^.form=sets) AND ((opsy=geq)OR(opsy=leq)) THEN
        (* set operation >=,<= *)
        IF opsy=leq THEN Emit(COM) END;
        Emit(ANDD); EmitLI(0); Emit(EQL); DEC(loadCount)
      ELSE
        CASE opsy OF  
            eql: inst := EQL   
          | neq: inst := NEQ   
          | grt: inst := GTR   
          | geq: inst := GEQ 
          | lss: inst := LSS 
          | leq: inst := LEQ 
          ELSE   CompilerError
        END;  
        EmitCompare(inst, Arithmetic(fat, lat))
      END;
      WITH fat DO
        (*mode := loadedMod;*)
        typtr := boolptr
      END  
    END  
  END Expression;  


  PROCEDURE ExpressionAndLoad;
    VAR lat: Attribut;
  BEGIN
    Expression(lat);
    Load(lat)
  END ExpressionAndLoad;


END MCP4ExpressionSys.  

