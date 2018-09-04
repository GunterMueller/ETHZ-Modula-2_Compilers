IMPLEMENTATION MODULE MCP4AttributSys;  (* Ch. Jacobi   v 5.10.81 *)

  (* $T-,R- *)
  
(* Attribut-System 
   for Pass 4 of the Compiler for the Lilith Computer *)

  
  IMPORT 
    MCBase, MCP4Global, MCP4CodeSys, MCMnemonics;

  FROM MCBase IMPORT  modnamlength,
    Idptr, Stptr, 
    Idclass, Idset, Structform, Stset,
    Varkind, Kindvar,  
    boolptr, charptr, intptr, cardptr, wordptr, 
    intcarptr, realptr, bitsetptr, addrptr;

  FROM MCP4Global IMPORT 
    loadCount, arithmeticRangeCheck, 
    Error, CompilerError, Assert;

  FROM MCP4CodeSys IMPORT
   
    (*Codesys*)
         Emit, Emit2, LinkageMark, InitCodeSys,
        
    (*SimpleCode*)
         EmitPacked, EmitLI, EmitLSW, EmitSSW, 
         UConstMul, UAddToTop,

    (*TypeSystem*)
         IsSetType;

  
  FROM MCMnemonics IMPORT                                                   
    LIW,  LLA,  LGA,  LSA,  LID,
    LLW,  LLD,
    SLW,  SLD,
    LGW,  LGD,  LXW,  LXD,
    SGW,  SGD,  SXW,  SXD,  SGWn,
    LSWn, LSTA,
    SSWn,
    FDIV, FNEG, FFCT,
    LSW,  LSD,  LSD0, LXB,  SSW,  SSD, SSD0, SXB,
    LODFW,LODFD,STOFV,COPT, DECS, PCOP,
    LEW,  LEA,  SEW,  LED,  SED,
    DIVV, UADD, UDIV, UMOD,
    ORR,  XORR, ANDD,
    MOV,  CHK,  CHKZ, UCHK,
    CHKS, GB1,  GB;


  PROCEDURE TestBaseType(ft: Stptr): Stptr;
    VAR lt1: Stptr;
  BEGIN lt1 := ft;
    IF ft^.form=subranges THEN
      lt1 := ft^.scalp;
      IF (lt1=cardptr) AND (ft^.max<=77777B) THEN lt1 := intcarptr END;
    END;
    RETURN lt1
  END TestBaseType;


  PROCEDURE ResultType(VAR fat1, fat2: Attribut): Stptr;
    VAR ft1, ft2: Stptr;
  BEGIN
    ft1 := fat1.typtr;
    IF ft1^.form=subranges THEN
      ft1 := ft1^.scalp;
    END;
    ft2 := fat2.typtr;
    IF ft2^.form=subranges THEN
      ft2 := ft2^.scalp;
    END;
    IF (ft1=intptr) OR (ft2=intptr) THEN RETURN intptr END;
    IF (ft1=cardptr) OR (ft2=cardptr) THEN RETURN cardptr END;
    IF ft1=boolptr THEN RETURN boolptr END;
    IF ft1^.form=enums THEN RETURN intptr END;
    IF (ft1=addrptr) OR (ft2=addrptr) THEN RETURN cardptr END;
    IF IsSetType(ft1) THEN RETURN bitsetptr END;
    (*IF ft1=charptr THEN RETURN charptr END;*)(* both arithmetic 
                                                  are correct *)
    IF (ft1=realptr) OR (ft2=realptr) THEN RETURN realptr END;
    RETURN cardptr
  END ResultType;


  PROCEDURE Arithmetic(VAR fat1, fat2: Attribut): ArithmeticType;
    VAR tptr: Stptr;
  BEGIN
    tptr := ResultType(fat1, fat2);
    IF tptr=cardptr THEN RETURN unSigned END;
    IF tptr=intptr THEN RETURN signed END;
    (*IF tptr=intcarptr THEN RETURN unSigned END;*)
    (*IF tptr=charptr THEN RETURN unSigned END;*)
    IF tptr=boolptr THEN RETURN logical END;
    IF tptr=bitsetptr THEN RETURN bitwise END;
    IF tptr=realptr THEN RETURN floating END;
    RETURN unSigned
  END Arithmetic;
  

  PROCEDURE RangeCheckForConstant(dest: Stptr; VAR fat: Attribut);
    (* tests assignment of a constant to an typed variable; 
       constant in an Attribut variable allows distinction
       of very negative integers from very big cardinals *)
    VAR base: Stptr;
  BEGIN 
    IF fat.mode=constantMod THEN
      base := TestBaseType(dest);
      IF dest^.form=subranges THEN
        IF base=intptr THEN
          IF (INTEGER(dest^.max)<fat.iValue) OR  
             (INTEGER(dest^.min)>fat.iValue) THEN Error(222) END;
        ELSE 
          IF (dest^.max<fat.value) OR (dest^.min>fat.value) THEN Error(222) END;
        END
      END;
      IF base=intptr THEN 
        IF TestBaseType(fat.typtr)=cardptr THEN Error(222) END
      ELSIF base=cardptr THEN 
        IF TestBaseType(fat.typtr)=intptr THEN Error(222) END
      ELSIF dest=charptr THEN 
        IF fat.value>377B THEN Error(222) END
      ELSIF dest^.form=enums THEN 
        IF fat.value>dest^.cstnr THEN Error(222) END
      END;
    END
  END RangeCheckForConstant;


  PROCEDURE RangeCheck(dest: Stptr; VAR fat: Attribut);
    (* may load fat if not constant *)
    VAR source: Stptr;
  BEGIN 
    IF fat.mode=constantMod THEN  RangeCheckForConstant(dest, fat);
    ELSIF (dest<>fat.typtr) AND arithmeticRangeCheck AND (SizeType(fat)=1) THEN
      source := fat.typtr; 
      Load(fat);
      IF TestBaseType(dest)=intptr THEN
        IF dest=intptr THEN 
          IF TestBaseType(source)=cardptr THEN
            Emit(CHKS)
          END
        ELSE (*dest<>intptr --> dest^.form=subranges, min<0  *)
          Assert(dest^.form=subranges); 
          IF (TestBaseType(source)=cardptr) THEN 
            IF INTEGER(dest^.max)<0 THEN Error(222) END;
            Emit(CHKS)
          END;
          EmitLI(dest^.min); EmitLI(dest^.max);
          Emit(CHK); DEC(loadCount, 2)
        END 
      ELSIF TestBaseType(dest)=cardptr THEN
        IF dest=addrptr THEN RETURN 
        ELSIF dest=cardptr THEN 
          IF TestBaseType(source)=intptr THEN
            Emit(CHKS)  
          END
        ELSE (*dest<>cardptr --> dest^.form=subranges max>77777B*)
          Assert(dest^.form=subranges); 
          IF (TestBaseType(source)=intptr) THEN 
            IF dest^.max>77777B THEN Error(222) END;
            Emit(CHKS)
          END;
          IF dest^.min<>0 THEN
            EmitLI(dest^.min); EmitLI(dest^.max); 
            Emit(UCHK); DEC(loadCount, 2);
          ELSIF dest^.max<>177777B THEN
            EmitLI(dest^.max); Emit(CHKZ); DEC(loadCount)
          END;
        END; 
      ELSIF dest^.form=subranges THEN (* but not of real card, int; maybe intcar*)
        IF dest^.min<>0 THEN 
          EmitLI(dest^.min); EmitLI(dest^.max); 
          Emit(UCHK); DEC(loadCount, 2)
        ELSE
          EmitLI(dest^.max); Emit(CHKZ); DEC(loadCount)
        END
      ELSIF (*CHR*) (dest=charptr) AND (TestBaseType(source)<>charptr) THEN
        EmitLI(377B); Emit(CHKZ); DEC(loadCount)
      ELSIF (*VAL*) (dest^.form=enums) AND (TestBaseType(source)<>dest) THEN 
        EmitLI(dest^.cstnr); Emit(CHKZ); DEC(loadCount)
      END
    END
  END RangeCheck;


  PROCEDURE SizeType(VAR fat: Attribut): INTEGER;   
    (* Return the size of the entity given by fat *)
  BEGIN   
    WITH fat DO  
      RETURN typtr^.size  
    END;
  END SizeType;  


  PROCEDURE SimpleType(VAR fat: Attribut): BOOLEAN;   
    (* Returns fat describes an simple typed attribut *)
  BEGIN  
    WITH fat.typtr^ DO  
      RETURN (size<=2) AND (form<>arrays) AND (form<>records)  
    END  
  END SimpleType;  


  PROCEDURE MarkVarAddr(VAR fat: Attribut);
  BEGIN
    LinkageMark;
    WITH fat DO
      Emit(moduleNo);
      Assert(addr<256);
      Emit(addr)
    END
  END MarkVarAddr;
  

  PROCEDURE Load(VAR fat: Attribut);
    (* Generate code to load the value of        
       fat onto the expression stack *)       
  BEGIN
    Assert(SizeType(fat)<=2);
    WITH fat DO
      CASE mode OF

        localMod, globalMod, externalMod, addrLoadedMod:
          IF addr<=255 THEN
            CASE mode OF

              globalMod:
                IF SizeType(fat)=1 THEN 
                  EmitPacked(LGW, addr);
                  INC(loadCount)
                ELSE  
                  Emit(LGD); Emit(addr);
                  INC(loadCount, 2)
                END 

            | externalMod:   
                IF SizeType(fat)=1 THEN 
                  Emit(LEW); INC(loadCount);
                  MarkVarAddr(fat)
                ELSE 
                  Emit(LED); INC(loadCount, 2);
                  MarkVarAddr(fat)
                END         

            | localMod:    
                IF SizeType(fat)=1 THEN             
                  EmitPacked(LLW, addr);
                  INC(loadCount)
                ELSE (*size 2*)
                  Emit(LLD); Emit(addr);
                  INC(loadCount, 2)
                END 

            | addrLoadedMod:         
                IF SizeType(fat)=1 THEN             
                  EmitLSW(addr)
                ELSE (* 2 *)
                  IF addr=0 THEN Emit(LSD0)
                  ELSE Emit(LSD); Emit(addr)
                  END;
                  INC(loadCount)
                END; 

            END
          ELSE 
            LoadAddr(fat); 
            Load(fat)
          END;

      | absolutMod:     
          EmitLI(addr);
          IF SizeType(fat)=1 THEN             
            Emit(LSWn);
          ELSE
            Emit(LSD0);
            INC(loadCount)
          END 

      | constantMod:
          EmitLI(value)

      | procedureMod:
          Emit(LIW); INC(loadCount);
          LinkageMark;
          Emit(procPtr^.globmodp^.modnum);
          Emit(procPtr^.procnum)

      | loadedMod: (* do nothing *)

      | indexMod:  
          IF SizeType(fat)=1 THEN 
            Emit(LXW);
            DEC(loadCount)
          ELSE
            (* size 2 is possible ! *)
            Emit(UADD); Emit(LSD0)
          END

      | byteIndexMod: 
          Emit(LXB); DEC(loadCount);
          Assert(SizeType(fat)=1)

      | doubleIndexMod:
          IF SizeType(fat)=2 THEN Emit(LXD)
          ELSE
            (* size 1 is possible ! *)
            UConstMul(2); Emit(LXW); DEC(loadCount)
          END

      | doubleConstMod:
          IF (r1<=15) OR (r2<=15) THEN
            EmitLI(r1);
            EmitLI(r2)     
          ELSE
            Emit(LID); Emit2(r1);  Emit2(r2);
            INC(loadCount, 2)
          END

      ELSE (*illegalMod, stringConstMod, stringTemplateMod*)  
          CompilerError;
      END;
      mode := loadedMod 
    END;
    IF loadCount>16 THEN Error(204) END
  END Load;


  PROCEDURE LoadAddr(VAR fat: Attribut);
    (* Generate code to load the address of                                     
       fat onto the expression stack *)
    VAR laddr: CARDINAL;
  BEGIN
    WITH fat DO
      CASE mode OF

        localMod, globalMod, externalMod:
          IF addr<=255 THEN
            CASE mode OF 
              globalMod:
                Emit(LGA); Emit(addr);
                INC(loadCount)

            | externalMod:
                Emit(LEA);
                MarkVarAddr(fat);
                INC(loadCount)

            | localMod:
                Emit(LLA); Emit(addr); INC(loadCount)
            END
          ELSE 
            laddr := addr-255; addr := 255;
            LoadAddr(fat); UAddToTop(laddr)
          END

      | absolutMod:
          EmitLI(addr)

      | stringTemplateMod:    
          (* imported strings are copied into the actual module*)
          IF addr=0 THEN EmitPacked(LGW, 2);
          ELSIF addr<=255 THEN Emit(LSTA); Emit(addr);
          ELSE EmitPacked(LGW, 2); UAddToTop(addr)
          END;
          INC(loadCount);

      | addrLoadedMod: 
          UAddToTop(addr)
  
      | indexMod: 
          Emit(UADD); DEC(loadCount)

      | doubleIndexMod: 
          Emit(COPT); Emit(UADD); Emit(UADD); DEC(loadCount)

      ELSE (*illegalMod, constantMod, procedureMod, stringConstMod,
             byteIndexMod, loadedMod, doubleConstMod*)
          CompilerError
      END;
      mode := addrLoadedMod; addr := 0
    END;
    IF loadCount>16 THEN Error(204) END
  END LoadAddr;


  PROCEDURE Store(VAR fat: Attribut);
  BEGIN
    Assert(SizeType(fat)<=2);
    WITH fat DO
      CASE mode OF

        addrLoadedMod:
          IF SizeType(fat)=1 THEN
            EmitSSW(addr)
          ELSE
            IF addr=0 THEN Emit(SSD0)
            ELSE Emit(SSD); Emit(addr)
            END; DEC(loadCount, 3)
          END

      | localMod:
          IF SizeType(fat)=1 THEN
            EmitPacked(SLW, addr);
            DEC(loadCount)
          ELSE
            Emit(SLD); Emit(addr); DEC(loadCount, 2)
          END

      | globalMod:
          IF SizeType(fat)=1 THEN
            EmitPacked(SGW, addr);
            DEC(loadCount)
          ELSE
            Emit(SGD); Emit(addr);
            DEC(loadCount, 2)
          END

      | externalMod:
          IF SizeType(fat)=1 THEN
            Emit(SEW);
            DEC(loadCount)
          ELSE
            Emit(SED);
            DEC(loadCount, 2)
          END;
          MarkVarAddr(fat)

      | indexMod: 
          Emit(SXW); DEC(loadCount, 3);
          Assert(SizeType(fat)=1)
      
      | doubleIndexMod:
          Emit(SXD); DEC(loadCount, 4);
          Assert(SizeType(fat)=2)

      | byteIndexMod: 
          Emit(SXB); DEC(loadCount, 3);
          Assert(SizeType(fat)=1)
 
      ELSE (*illegalMod, loadedMod, procedureMod, doubleConstMod,
             stringConstMod, constantMod, absolutMod, stringTemplateMod*)
          CompilerError
      END;
      mode := illegalMod (* prevents further use *)
    END
  END Store;


  PROCEDURE LoadDynHigh(VAR fat: Attribut);
  BEGIN
    WITH fat DO
      Assert((typtr^.form=arrays) AND typtr^.dyn);
      IF dynArrLevelDiff>0 THEN 
        IF dynArrLevelDiff=1 THEN 
          Emit(GB1)
        ELSE 
          Emit(GB); Emit(dynArrLevelDiff)
        END;
        EmitPacked(LSW, dynArrOffset)
      ELSE EmitPacked(LLW, dynArrOffset) END
    END;
    INC(loadCount)
  END LoadDynHigh;


  PROCEDURE PreAssign(VAR fat: Attribut);
    (* Generate code to prepare the attribut such that 
       a subsequent value may be loaded and assigned 
       to with assign *)
  BEGIN
    IF (SizeType(fat)>2) THEN LoadAddr(fat)      
    ELSE
      CASE fat.mode OF
          addrLoadedMod, externalMod, globalMod, localMod:
            IF fat.addr>255 THEN LoadAddr(fat) END
        | absolutMod: LoadAddr(fat) 
        | doubleIndexMod:
            IF SizeType(fat)<>2 THEN LoadAddr(fat) END      
        | indexMod:
            IF SizeType(fat)<>1 THEN LoadAddr(fat) END 
        | byteIndexMod: (*nothing*)     
        ELSE CompilerError 
      END
    END
  END PreAssign;


  PROCEDURE Assign(VAR desAT, expAT: Attribut);
    (* code for assignment desAT := expAT;
       dynamic array not allowed, see Language definition *)
    VAR size: CARDINAL;
  BEGIN
    size := SizeType(desAT); (* use desAT in case of variants! *)
    IF expAT.mode=stringConstMod THEN CompilerError END;
    IF (size>2) OR (expAT.mode=stringTemplateMod) THEN
      IF (expAT.mode=stringTemplateMod) THEN LoadAddr(desAT) END;
      Assert((desAT.mode=addrLoadedMod) AND (desAT.addr=0));
      LoadAddr(expAT);
      EmitLI(size);
      Emit(MOV); 
      DEC(loadCount, 3)
    ELSE (* size byte(then indexed), word, double word *)
      RangeCheck(desAT.typtr, expAT);
      Load(expAT);
      Store(desAT)
    END;
    desAT.mode := illegalMod;
    expAT.mode := illegalMod
  END Assign;


BEGIN
  InitCodeSys
END MCP4AttributSys.
