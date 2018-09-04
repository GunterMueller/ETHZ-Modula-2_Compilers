IMPLEMENTATION MODULE MCP4CallSys;   (* Ch. Jacobi 5.4.81; version: 6.6.81 *) 

  (* $T-,R- *)

(* procedure calls 
   for Pass 4 of the Compiler for the Lilith Computer *)

  FROM MCBase IMPORT  
    Idptr, Stptr, noprio,
    Idclass, Structform, 
    Varkind, Stpures, Stfuncs,
    boolptr, intptr, cardptr, wordptr, intcarptr, 
    realptr, addrptr, charptr,
    mainmodp, Symbol;

  FROM MCP4Global IMPORT 
    level, loadCount, arithmeticRangeCheck, 
    blockNptr, nptr,
    GetSymbol, sy,  
    Error, CompilerError, Assert;

  FROM MCP4CodeSys IMPORT
   
    (*Codesys*)
         Emit, Emit2, LinkageMark,  
        
    (*SimpleCode*)
         EmitLI, EmitCL, UConstMul, UAddToTop, 

    (*TypeSystem*)
         IsArrayType, ByteSize, IsSetType,
    
    (*BlockSystem*)
         CodeBody;

  FROM MCP4AttributSys IMPORT
    ArithmeticType, AtMode, Attribut, ModeSet,
    HasAlreadyCode, TestBaseType, Arithmetic, ResultType,
    RangeCheck, SizeType, SimpleType,
    Load, LoadAddr, Store,
    LoadDynHigh, PreAssign;

  FROM MCP4ExpressionSys IMPORT
    Expression, Designator, ExpressionAndLoad;

  FROM MCMnemonics IMPORT
    LSA,
    GB1, GB, CX, CI, CF, FFCT,
    STORE, STOT, LODFW, LODFD, COPT, DECS, STOFV,
    TRA, TRAP, READ, WRITE,
    ADD, UADD, SUB,  USUB,
    SHR, SHL,  ANDD, ORR, ABSS, BIT, COM,
    FABS, CHK, UCHK, CHKZ, PACK;
 
                    
  PROCEDURE ProcFuncCall(VAR fat: Attribut);   


    PROCEDURE Forget(VAR fat: Attribut);
    BEGIN
      IF fat.mode=addrLoadedMod THEN
        (* forget the top of the expression stack *)
        Emit(STOT); Emit(DECS); DEC(loadCount)
      END
    END Forget;


    PROCEDURE StandFunc(VAR fat: Attribut; fCalling: Stfuncs);   
      VAR
        lat1, lat2 : Attribut;
        lsize: CARDINAL; 
        ltyp: ArithmeticType; 
        lTypP: Stptr;
    BEGIN
      CASE fCalling OF  
          higf: (* HIGH *)  
            Designator(fat); Forget(fat);  
            WITH fat DO  
              Assert(IsArrayType(typtr));  
              WITH typtr^ DO
                IF dyn THEN
                  LoadDynHigh(fat); mode := loadedMod;
                  typtr := cardptr   
                ELSE   
                  Assert(ixp^.form=subranges);  
                  mode := constantMod;  
                  value := ixp^.max;  
                  typtr := ixp^.scalp   
                END  
              END  
            END  

        | sizf: (*SIZE *)  
            Designator(fat); Forget(fat);  
            WITH fat DO  
              IF IsArrayType(typtr) AND typtr^.dyn THEN  
                LoadDynHigh(fat); mode := loadedMod;
                IF ByteSize(typtr^.elp) THEN
                  EmitLI(1); Emit(SHR); DEC(loadCount);
                  UAddToTop(1) 
                ELSE
                  UAddToTop(1); 
                  UConstMul(typtr^.elp^.size)
                END
              ELSE 
                mode := constantMod;  
                value := SizeType(fat)  
              END;  
              typtr := intcarptr   
            END  

        | adrf: (* ADR *)  
            Designator(fat);  
            IF fat.mode=byteIndexMod THEN Error(206); fat.mode := indexMod END;
            LoadAddr(fat); fat.mode := loadedMod;
            fat.typtr:= addrptr  

        | oddf: (* ODD *)  
            Expression(fat); Load(fat);
            fat.typtr := boolptr;  
            EmitLI(1); Emit(ANDD); DEC(loadCount)

        | chrf: (* CHR *)  
            Expression(fat); 
            IF arithmeticRangeCheck THEN
              RangeCheck(charptr, fat);
            ELSE
              EmitLI(377B); Emit(ANDD); DEC(loadCount);
            END;
            fat.typtr := charptr  

        | ordf: (* ORD *)  
            Expression(fat); 
            RangeCheck(cardptr, fat);
            fat.typtr := cardptr  

        | valf:   
            Assert((sy=namesy) AND (nptr^.klass=types));
            lTypP := nptr^.idtyp; GetSymbol;
            GetSymbol; (*comma*)
            Expression(fat); 
            RangeCheck(lTypP, fat);
            fat.typtr := lTypP  

        | absf:  (* ABS *)
            Expression(fat); 
            ltyp := Arithmetic(fat, fat);
            IF ltyp = signed  THEN
              Load(fat); Emit(ABSS)
            ELSIF ltyp=floating THEN 
              Load(fat);  Emit(FABS)
            ELSE 
              Assert(ltyp=unSigned)
            END
  
        | capf:  (* CAP *)
            Expression(fat); Load(fat);  
            EmitLI(137B); Emit(ANDD); DEC(loadCount)

        | fltf:  (* FLOAT *)
            Expression(fat); Load(fat); fat.typtr := realptr;
            INC(loadCount); 
            Emit(FFCT); Emit(0)

        | trcf:  (* TRUNC *)
            Expression(fat); Load(fat); fat.typtr := cardptr; 
            DEC(loadCount); 
            Emit(FFCT); Emit(2)
      END  
    END StandFunc;  


  PROCEDURE StandProc(fCalling: Stpures);   

    PROCEDURE TransfProc;
    (* Treat call of procedure TRANSFER *)
      VAR lat: Attribut; (* descriptor of parameter *)
    BEGIN
      (* first parameter: old coroutine *)
      Designator(lat); LoadAddr(lat);
      GetSymbol; (*comma*)
      (* second parameter: new coroutine *)
      Designator(lat); 
      LoadAddr(lat);
      Emit(TRA); DEC(loadCount, 2);
      IF blockNptr^.priolev=noprio THEN Emit(0) ELSE Emit(1) END
    END TransfProc;

    PROCEDURE NewPrProc; 
    (* Treat call of procedure NEWPROCESS *)
      VAR lat: Attribut; (* descriptor of parameter *)
          i: CARDINAL;
    BEGIN
      FOR i := 1 TO 3 DO
        (* parameter transmission as for user procedure *)
        ExpressionAndLoad;
        GetSymbol; (*comma*)
      END;
      Designator(lat); LoadAddr(lat);
      Emit(CX); Emit(0); Emit(2); DEC(loadCount, 4)
    END NewPrProc;

    PROCEDURE IncDecCheck(ft: Stptr; isInc: BOOLEAN);
      (* runtimetests for INC, DEC; assume increment 0<=inc<=77777B *)
    BEGIN
      IF arithmeticRangeCheck THEN
        IF isInc THEN
          IF ft^.form=subranges THEN
            IF TestBaseType(ft)=intptr THEN
              EmitLI(ft^.min); EmitLI(ft^.max);
              Emit(CHK); DEC(loadCount, 2)
            ELSE
              IF ft^.max<177777B THEN 
              (* both integer and cardinal! *)
                EmitLI(ft^.max); Emit(CHKZ); DEC(loadCount)
              END
            END
          ELSIF ft=charptr THEN 
            EmitLI(377B); Emit(CHKZ); DEC(loadCount)
          ELSIF ft^.form=enums THEN 
            EmitLI(ft^.cstnr); Emit(CHKZ); DEC(loadCount)
          ELSIF ft=boolptr THEN 
            EmitLI(1); Emit(CHKZ); DEC(loadCount)
          END
        ELSE (*dec*)
          IF ft^.form=subranges THEN
            IF TestBaseType(ft)=intptr THEN
              IF ft^.min>100000B THEN 
                EmitLI(ft^.min); EmitLI(ft^.max);
                Emit(CHK); DEC(loadCount, 2)
              END;
            ELSE
              IF ft^.min>0 THEN 
                EmitLI(ft^.min); EmitLI(ft^.max);
                Emit(UCHK); DEC(loadCount, 2)
              END;
            END
          END
        END
      END
    END IncDecCheck;

    VAR 
      lat1, lat2, lat3: Attribut;
      AType: ArithmeticType;
      lLoadCount: CARDINAL;
      simpleInc: BOOLEAN;
      destt: Stptr;
  BEGIN  
    lLoadCount := loadCount;
    CASE fCalling OF   
        incp, decp: (* INC, DEC(lat1, lat2) *)
          Designator(lat1); 
          PreAssign(lat1);
          IF lat1.mode IN HasAlreadyCode THEN 
            (* record fields: not loading addresses results in shorter code, 
               but more memory accesses are needed *) 
            IF lat1.mode=byteIndexMod THEN Error(206); lat1.mode := indexMod END;
            LoadAddr(lat1); 
            Emit(COPT);   (* address loaded twice *)
            INC(loadCount);
          END;
          lat3 := lat1; Load(lat3); (* save lat1 for subsequent store *)
          destt := TestBaseType(lat3.typtr);
          IF destt=intcarptr THEN destt := cardptr END;
          IF sy=comma THEN GetSymbol; 
            Expression(lat2); 
            simpleInc := (TestBaseType(lat2.typtr)=intcarptr);
            RangeCheck(destt, lat2);
            Load(lat2);
          ELSE 
            simpleInc := TRUE;
            EmitLI(1) 
          END;
          AType := Arithmetic(lat3, lat3); (* twice lat1 !*)
          IF fCalling=incp THEN
            IF AType=signed THEN Emit(ADD)
            ELSE (*unsigned, logical*) Emit(UADD)
            END;
          ELSE (*decp*)
            IF AType=signed THEN Emit(SUB)
            ELSE (*unsigned, logical*) Emit(USUB)
            END;
          END;
          DEC(loadCount);
          IF simpleInc THEN IncDecCheck(lat3.typtr, fCalling=incp)
          ELSE
            lat3.typtr := TestBaseType(lat3.typtr);
            IF (lat3.typtr^.form=enums) 
               OR (lat3.typtr=charptr) OR (lat3.typtr=boolptr) THEN
               lat3.typtr := cardptr
            END;
            RangeCheck(lat1.typtr, lat3);
          END;
          Store(lat1);
               
      | halp: (* HALT *)  
          EmitLI(10); Emit(TRAP) 

      | inlp, exlp: (* INCL, EXCL(lat1, lat2) *)   
          Designator(lat1); LoadAddr(lat1);
          GetSymbol; 
          Expression(lat1);
          IF lat1.mode=constantMod THEN 
            IF lat1.value>15 THEN Error(222) END;
            EmitLI(lat1.value);  
          ELSE
            Load(lat1);
            IF arithmeticRangeCheck THEN EmitLI(15); Emit(CHKZ); DEC(loadCount) END;
          END;
          Emit(COPT);           (* bitnumber loaded twice *) 
          EmitLI( 177777B * ORD(fCalling=inlp) );
          Emit(PACK);
          DEC(loadCount, 3);

      | trsp: (* TRANSFER *)
         TransfProc

      | nprp: (* NEWPROCESS *)
          NewPrProc
      
      END;  
      loadCount := lLoadCount (* To undo any INC(LoadCount)'s *)
                              (* of CODE which can't be counted *)
    END StandProc;  



    PROCEDURE LoadParam(fsp: Stptr);          
      VAR lat: Attribut; LNP: Idptr;  
  
      PROCEDURE DynParam(VAR fat: Attribut; IsBlock: BOOLEAN);   
        VAR s: CARDINAL;
      BEGIN  
        WITH fat DO  
          WITH typtr^ DO
            Assert((form=arrays) OR IsBlock);  
            IF (form=arrays) AND dyn THEN 
              LoadAddr(fat);  
              LoadDynHigh(fat);  
              IF IsBlock THEN
                IF ByteSize(elp) THEN
                  Emit(LSA); Emit(1); EmitLI(1); Emit(SHR) 
                ELSE s := elp^.size;
                  UConstMul(s); 
                  IF s>1 THEN
                    IF s<=256 THEN Emit(LSA); Emit(s-1)
                    ELSE EmitLI(s-1); Emit(UADD) END
                  END
                END
              END
            ELSE  
              IF IsBlock THEN
                IF mode IN ModeSet{globalMod, localMod, addrLoadedMod,
                                   externalMod, indexMod, doubleIndexMod, 
                                   absolutMod, stringTemplateMod} THEN 
                  LoadAddr(fat); EmitLI(size-1)  
                ELSE Error(201) END  
              ELSE
                LoadAddr(fat);  
                WITH ixp^ DO  
                  IF max>=min THEN EmitLI(max-min) 
                  ELSE EmitLI(177777B-min+max+1) END;  
                END  
              END
            END  
          END
        END  
      END DynParam;  
  
    BEGIN (* LoadParam *)  
      Assert((fsp<>NIL) AND (fsp^.form=proctypes));   
      LNP := fsp^.fstparam;   
      WHILE LNP<>NIL DO  
        WITH LNP^ DO  
          Expression(lat);  
          IF (vkind=copyparam) OR (vkind=varparam) THEN  
            IF (vkind=varparam) AND (lat.mode=byteIndexMod) THEN
              Error(206)  
            ELSIF lat.mode=loadedMod THEN 
              Error(201); (*occurs through type converters*)
            ELSIF (idtyp^.form=arrays) AND idtyp^.dyn THEN
              DynParam(lat, (idtyp^.elp=wordptr))  
            ELSE
              LoadAddr(lat)  
            END
          ELSE  
            RangeCheck(idtyp, lat);
            Load(lat)  
          END;  
          LNP := vlink;  
          IF LNP<>NIL THEN 
            GetSymbol (*comma*)
          END  
        END  
      END;  
      GetSymbol (*rparent*)  
    END LoadParam;  


    VAR 
      lpsptr: Stptr;  
      lLoadCount: CARDINAL;
      storeGen: BOOLEAN;

  BEGIN (*ProcFuncCall*)  
    WITH fat DO  
      IF mode=procedureMod THEN
        IF procPtr^.isstandard THEN  
          IF procPtr^.klass=funcs THEN 
            StandFunc(fat, procPtr^.fname)  
          ELSE (* klass=pures*)
            StandProc(procPtr^.pname)  
          END;  
          GetSymbol; (*rparent*)  
        ELSIF procPtr^.klass=mods THEN
          EmitCL(procPtr^.procnum);
          GetSymbol; (*rparent*)
        ELSIF procPtr^.codeproc AND NOT procPtr^.externalaccess THEN
          (*used either inline or as procedure; priority cannot be used inline*)
          lLoadCount := loadCount; 
          LoadParam(procPtr^.idtyp);
          loadCount := lLoadCount; 
          CodeBody(procPtr);
          IF procPtr^.klass=funcs THEN
            typtr := procPtr^.idtyp^.funcp; 
            mode := loadedMod;
            INC(loadCount, typtr^.size)
          END   
        ELSE 
          lpsptr := procPtr^.idtyp;
          WITH lpsptr^ DO  
            storeGen := FALSE;
            IF (rkind=funcs) THEN
              IF loadCount>0 THEN
                Emit(STORE);
                storeGen := TRUE
              END;
              lLoadCount := loadCount 
            END;  
            LoadParam(lpsptr);  
            (*Call*)
            WITH procPtr^ DO
              IF (plev=level+1) THEN
                (*local procedure*)
                EmitCL(procnum)
              ELSIF plev>1 THEN 
                (*intermediate level procedure*)
                Emit(GB);
                Emit(level - plev + 1);
                Emit(CI); Emit(procnum)
              ELSIF (plev=1) AND (globmodp=mainmodp) THEN  
                (*global procedure*)
                EmitCL(procnum)
              ELSE (*imported procedure*)
                Emit(CX);
                LinkageMark;
                Emit(globmodp^.modnum);
                Emit(procnum)
              END
            END;
            IF rkind=funcs THEN  
              typtr := funcp; mode := loadedMod;   
              IF typtr^.size=1 THEN 
                IF storeGen THEN Emit(LODFW) END;
                loadCount := lLoadCount+1
              ELSE
                Assert(typtr=realptr);
                IF storeGen THEN Emit(LODFD) END;
                loadCount := lLoadCount+2
              END
            ELSE loadCount := 0
            END  
          END
        END  
      ELSE (* procedure variable *)
        lLoadCount := loadCount;
        Load(fat);
        storeGen := FALSE;
        IF (typtr^.rkind=funcs) AND (lLoadCount>0) THEN 
          Emit(STOFV); storeGen := TRUE
        ELSE Emit(STOT)
        END;
        loadCount := 0;
        LoadParam(typtr);
        Emit(CF); Emit(DECS);
        IF typtr^.rkind=funcs THEN
          typtr := typtr^.funcp; mode := loadedMod;   
          IF typtr^.size=1 THEN 
            IF storeGen THEN Emit(LODFW) END;
            loadCount := lLoadCount+1
          ELSE
            Assert(typtr=realptr);
            IF storeGen THEN Emit(LODFD) END;
            loadCount := lLoadCount+2
          END
        ELSE loadCount := 0
        END
      END  
    END  
  END ProcFuncCall;


END MCP4CallSys.
  
