(*************************************
*                                    *  
*    MODULA 2 MULTI-PASS COMPILER    *  
*    ****************************    *  
*                                    *  
*    Pass 4: code generation         *  
*    for Lilith computer             *  
*    Version          5.4.81         *  
*                                    *
*    Christian Jacobi                *  
*    Institut fuer Informatik        *  
*    ETH-Zuerich                     *  
*    CH-8092 Zuerich                 *  
*                                    *  
*************************************)

  (* $T-,R- *)

MODULE Pass4;  
  
  FROM Storage IMPORT 
    ALLOCATE, DEALLOCATE;

  FROM MCBase IMPORT
    modnamlength,
    Idptr, Stptr, 
    Idclass, Idset, Structform, Stset,
    Varkind, Kindvar, Stpures, Stfuncs,
    intptr, cardptr, 
    Symbol;

  FROM MCP4Global IMPORT 
    loadAddress, level,
    loadCount, spPosition, 
    blockNptr,
    CloseIO,
    GetSymbol, sy, val, 
    nptr, controlRangeCheck, arithmeticRangeCheck,
    Error, CompilerError, Assert;

  FROM MCP4CodeSys IMPORT
   
    (*Codesys*)
        PC, Emit, Emit2, 
        Insert, Insert2, MoveCode,
        MarkLong,  UpdateLong,
        MarkShort, UpdateShort,
        LinkageMark, 
        
    (*SimpleCode*)
        EmitLI, Emit2GivePC, Fixup2,

    (*BlockSystem*)
        GenBlockEntry, GenBlockReturn, TerminateBlock, GenCodeBlock;

  FROM MCP4AttributSys IMPORT
    AtMode, Attribut,
    TestBaseType, Arithmetic,
    RangeCheck, RangeCheckForConstant, SizeType, SimpleType,
    Load, LoadAddr, Store,
    PreAssign, Assign;

  FROM MCMnemonics IMPORT                                                   
    JPC, JP, JPFC, JPF, JPBC, JPB, TRAP,
    FOR1, FOR2, ENTC, EXC,
    DECS, CHKS;

  FROM MCP4ExpressionSys IMPORT 
    EnterWith, ExitWith, 
    Designator, Expression, ExpressionAndLoad;

  FROM MCP4CallSys IMPORT
    ProcFuncCall;


  PROCEDURE Skip(x1, x2: Symbol);
  BEGIN
    WHILE (sy<>endsy) AND (sy<>x1) AND (sy<>x2) AND (sy<>eop) DO
      IF (sy=casesy) OR (sy=ifsy) OR (sy=withsy) 
         OR (sy=loopsy) OR (sy=forsy) OR (sy=whilesy)
      THEN 
        GetSymbol;
        Skip(endsy, endsy) 
      END;
      GetSymbol
    END
  END Skip;

  PROCEDURE Assignment;   
    VAR lat1, lat2: Attribut;  
  BEGIN
    Designator(lat1); PreAssign(lat1);  
    GetSymbol;
    Expression(lat2); Assign(lat1, lat2)  
  END Assignment;  


  PROCEDURE IfStatement;   
    TYPE
      ListPtr = POINTER TO JumpRecord;
      JumpRecord = 
        RECORD nextPtr: ListPtr;
          nextJump: CARDINAL;
          endJump: CARDINAL
        END;
    VAR 
      lat: Attribut;
      lp, jumpList: ListPtr;
      shift, curPC, c: CARDINAL;

    PROCEDURE NewListEntry;
      VAR lp: ListPtr;
    BEGIN NEW(lp);
      lp^.nextPtr := jumpList;
      jumpList := lp
    END NewListEntry; 

  BEGIN (*IfStatement*) 
    (* analysis *)
    jumpList := NIL; 
    LOOP Expression(lat);
      IF lat.mode=constantMod THEN
        IF BOOLEAN(lat.value) THEN
          StatSeq3(endsy, elsifsy, elsesy); 
          IF sy<>endsy THEN Skip(endsy, endsy) END;
          EXIT
        ELSE Skip(elsesy, elsifsy);
          IF sy <> elsifsy THEN EXIT END;  
          GetSymbol
        END 
      ELSE
        NewListEntry;
        Load(lat); DEC(loadCount);
        jumpList^.nextJump := PC; Emit(JPFC); Emit(0);
        StatSeq3(endsy, elsifsy, elsesy); 
        jumpList^.endJump := PC; 
        IF sy<>endsy  THEN Emit(JPF); Emit(0)
        END;
        IF sy <> elsifsy THEN EXIT END;  
        GetSymbol 
      END 
    END;  
    IF sy = elsesy THEN GetSymbol;  
      (*the occurence of an else can be detected by jumpList^.endJump<>PC*)
      StatSeq1(endsy)  
    END;  
    GetSymbol; (* skip endsy *)  

    (* compute total displacement *)
    shift := 0;
    lp := jumpList;
    WHILE lp<>NIL DO
      (* test for the jump to the end *)
      (* c gets the length of the jump instruction to the end *)
      IF (ORD(PC)+shift-lp^.endJump)=0 THEN c := 0 
      ELSIF (ORD(PC)+shift-lp^.endJump)>(255+1) THEN INC(shift); c := 3 
      ELSE c := 2 END;
      (* test for the jump to the next test or else part *)
      IF (c+lp^.endJump-lp^.nextJump)>(255+1) THEN INC(shift) END;
      lp := lp^.nextPtr
    END;

    (* fix jump adresses *)
    lp := jumpList;
    curPC := PC;
    WHILE lp<>NIL DO
      (* handle the jump to the end *)
      (* c gets the length of the jump instruction to the end *)
      IF lp^.endJump<curPC THEN
        IF shift>0 THEN MoveCode(lp^.endJump, curPC-1, shift) END;
        IF (ORD(PC)-shift-lp^.endJump)>(255+1) THEN
          Insert(lp^.endJump+shift-1, JP); 
          Insert2(lp^.endJump+shift, ORD(PC)-(lp^.endJump+shift));
          DEC(shift); c := 3
        ELSE 
          Insert(lp^.endJump+shift+1, ORD(PC)-(lp^.endJump+shift+1));
          c := 2
        END
      ELSE c := 0  (*no else part*)
      END;
      curPC := lp^.nextJump;
      (* handle the jump to the next test or else part *)
      IF shift>0 THEN MoveCode(lp^.nextJump, lp^.endJump-1, shift) END;
      c := c+lp^.endJump-lp^.nextJump-1;
      IF c>255 THEN
        Insert(lp^.nextJump+shift-1, JPC); 
        Insert2(lp^.nextJump+shift, c+1);
        DEC(shift)
      ELSE
        Insert(lp^.nextJump+shift+1, c);
      END;
      lp := lp^.nextPtr
    END
  END IfStatement;

   
  PROCEDURE ForStatement;   
    VAR 
      cntat, lat: Attribut;  
      step: INTEGER;  
      loopPC, exPC: INTEGER;

    PROCEDURE LoadAndTest(VAR fat: Attribut);
      (* special runtime test; control variable handled
         as integer by hardware *)
      VAR bt: Stptr;
    BEGIN bt := TestBaseType(fat.typtr);
      IF fat.mode=constantMod THEN
        IF (bt=cardptr)
          (* means cardinal > maxint! usually int or intcar or scalar *) 
        THEN Error(222) END;
        RangeCheck(cntat.typtr, fat);
        Load(fat) 
      ELSE
        Load(fat);
        IF (TestBaseType(cntat.typtr)=cardptr) AND (TestBaseType(fat.typtr)=cardptr) THEN
          (*sorry i'm to lazy *)
          IF arithmeticRangeCheck THEN Emit(CHKS) END; 
          RangeCheck(cntat.typtr, fat)
        ELSE                                   
          RangeCheck(cntat.typtr, fat)
        END
      END
    END LoadAndTest;

  BEGIN  
    Designator(cntat); LoadAddr(cntat);  
    GetSymbol; (*comma*)  
    Expression(lat); LoadAndTest(lat);  
    GetSymbol; (*tosy*)  
    Expression(lat); LoadAndTest(lat);  
    DEC(loadCount, 3);
    IF sy=bysy THEN GetSymbol; GetSymbol;  
      step := val  
    ELSE step := 1 END;  
    Emit(FOR1);
    IF (step=0) OR (step>127) OR (step<-128) THEN Error(202) END;
    IF step>0 THEN Emit(0) ELSE Emit(1) END;
    Emit2GivePC(exPC);
    loopPC := PC;
    INC(spPosition, 2);
    StatSeq1(endsy); GetSymbol;  
    DEC(spPosition, 2);
    Emit(FOR2);
    Emit(CARDINAL(step) MOD 400B);
    Emit2(loopPC-PC); Fixup2(exPC)
  END ForStatement;  
    

  PROCEDURE WithStatement;   
    VAR lat: Attribut;  
  BEGIN  
    Designator(lat); EnterWith(lat);   
    StatSeq1(endsy);  
    GetSymbol; ExitWith  
  END WithStatement;  


  MODULE LoopSys;
    IMPORT
      PC, Symbol, GetSymbol, StatSeq1,
      spPosition,
      Emit, Emit2, JP, JPB, DECS,
      MarkLong, UpdateLong; 
    EXPORT 
      LoopStatement, ExitStatement; 
   
    VAR 
      currendLoopPC: INTEGER;
      loopSPpos: INTEGER;


    PROCEDURE LoopStatement;   
      VAR lPC, outerLoopPC: INTEGER;
          outsideSPpos: INTEGER;
    BEGIN
      outerLoopPC  := currendLoopPC; currendLoopPC := 0;
      outsideSPpos := loopSPpos; loopSPpos := spPosition;
      lPC := PC;
      StatSeq1(endsy); GetSymbol; 
      lPC := PC-lPC+1;
      IF lPC>255 THEN Emit(JP); Emit2(-lPC)
      ELSE Emit(JPB); Emit(lPC);
      END;
      UpdateLong(currendLoopPC); currendLoopPC := outerLoopPC;
      loopSPpos := outsideSPpos
    END LoopStatement;  
    

    PROCEDURE ExitStatement;   
      VAR i: INTEGER;
    BEGIN  
      FOR i := loopSPpos+1 TO spPosition DO 
        Emit(DECS)
      END;
      Emit(JP); MarkLong(currendLoopPC) (* must use long jump *)
    END ExitStatement;  
    

  BEGIN
    currendLoopPC := 0 (*should never be used; 
                         but prevents error from exit without loop*)
  END LoopSys;    


  PROCEDURE RepeatStatement;    
    VAR lPC: INTEGER;
  BEGIN
    lPC := PC;
    StatSeq1(untilsy); GetSymbol;  
    ExpressionAndLoad; DEC(loadCount);
    lPC := PC-lPC+1;
    IF lPC>255 THEN Emit(JPC); Emit2(-lPC)
    ELSE Emit(JPBC); Emit(lPC)
    END
  END RepeatStatement;  


  PROCEDURE WhileStatement;   
    VAR startPC, jumpOutPC, forwardOffset: INTEGER;
  BEGIN
    startPC := PC;
    ExpressionAndLoad; DEC(loadCount);
    jumpOutPC := PC; Emit(JPFC); Emit(0);
    StatSeq1(endsy);  
    forwardOffset := PC-jumpOutPC+1;
    IF (PC-startPC)>(255-1) THEN (*backjump is long*)
      IF forwardOffset>(255-1) THEN (*two long jumps*)
        MoveCode(jumpOutPC+2, PC-1, 1);
        Insert(jumpOutPC, JPC); Insert2(jumpOutPC+1, forwardOffset+2)
      ELSE (*only backjump is longjump*)
        Insert(jumpOutPC+1, forwardOffset+1)
      END;
      Emit(JP); Emit2(startPC-PC)
    ELSE (*all short jumps*)
      Emit(JPB); Emit(PC-startPC);
      Insert(jumpOutPC+1, forwardOffset)
    END;
    GetSymbol  
  END WhileStatement;  

     
  PROCEDURE CaseStatement;                          
    (* the case expression is assumed to have integer type *)

    TYPE CasePtr = POINTER TO CaseRec;
      CaseRec = 
        RECORD
          cval: INTEGER;
          casePC: INTEGER;
          next: CasePtr
        END;

    VAR elsePC, tabPC: INTEGER;
      cHeader: CasePtr; (* header of cicular ordered list *)
      lat: Attribut;

    PROCEDURE CaseLabels;
      VAR cp: CasePtr; lval, i: INTEGER;

      PROCEDURE EnterCaseLabel(VAR fcp: CasePtr; fval: INTEGER);
        (* build new element in linear list of fcp with value fval *)
        VAR lp: CasePtr;
      BEGIN
        NEW(lp);
        WITH lp^ DO
          cval := fval;
          next := fcp; fcp := lp
        END
      END EnterCaseLabel;
      
      PROCEDURE MarkCase(fcp: CasePtr);                       
        (* the linear list from fcp is inserted into the list of cHeader *)
        VAR ival: INTEGER;
            currcp, lp, lp2: CasePtr;
      BEGIN
        WHILE fcp<>NIL DO
          WITH fcp^ DO (*take currcp out of the linear list*)
            currcp := fcp; casePC := PC; fcp := next;
          END;
          (*include currcp in circular list*)
          ival := currcp^.cval;
          cHeader^.cval := ival; (*garantees terminating of insert loop*)
          lp2 := cHeader;        (*predecessor*)
          lp := cHeader^.next;   (*current*)
          WHILE lp^.cval < ival DO
            lp2 := lp; lp := lp^.next
          END;
          IF (lp<>cHeader) AND (lp^.cval=ival) THEN Error(223) END;
          currcp^.next := lp; lp2^.next := currcp
        END
      END MarkCase;

    BEGIN (*CaseLabels*)
      cp := NIL;
      REPEAT lval := val;
        GetSymbol;
        IF sy = range THEN GetSymbol;
          FOR i := lval TO val DO EnterCaseLabel(cp, i) END;
          GetSymbol;
        ELSE EnterCaseLabel(cp, lval); 
        END;
      UNTIL sy = colon; GetSymbol;
      MarkCase(cp)
    END CaseLabels;

    PROCEDURE CaseTable;
      VAR cp, cp2: CasePtr;
          upPC: INTEGER;
          i, k: INTEGER;
    BEGIN
      cp := cHeader^.next;
      IF cp=cHeader THEN (*empty*)
        Emit2(1); Emit2(0); Emit2(elsePC-PC)
      ELSE                    
        WITH cp^ DO
          k := cval;
          Emit2(k);          (*low*) 
          Emit2GivePC(upPC); (*high*)
          Emit2(elsePC-PC);  (*else*) 
          Emit2(casePC-PC);  (*first*)
          cp2 := cp; cp := next; DISPOSE(cp2)
        END;
        WHILE cp<>cHeader DO
          WITH cp^ DO
            FOR i := 2 TO cval-k DO (* k+1 .. cval-1 are empty*)
              Emit2(elsePC-PC) (*else*)
            END;
            k := cval;
            Emit2(casePC-PC); (*jump*)
            cp2 := cp; cp := next; DISPOSE(cp2)
          END
        END; 
        Insert2(upPC, k)
      END 
    END CaseTable;

  BEGIN (*CaseStatement*)
    NEW(cHeader); (*header of empty cicular ordered list*)
    WITH cHeader^ DO next := cHeader; cval := 0 END;
    Expression(lat); Load(lat); DEC(loadCount);
    Emit(ENTC);
    Emit2GivePC(tabPC); INC(spPosition);
    WHILE sy = ofsy DO GetSymbol;           
      CaseLabels; StatSeq3(ofsy, elsesy, endsy); Emit(EXC)         
    END;  
    elsePC := PC;
    IF sy = elsesy THEN GetSymbol; 
      StatSeq1(endsy); Emit(EXC)   
    ELSIF controlRangeCheck THEN 
      EmitLI(4); DEC(loadCount); Emit(TRAP)
    END;
    GetSymbol;
    Fixup2(tabPC); CaseTable; DEC(spPosition);
    DISPOSE(cHeader)
  END CaseStatement; 


  PROCEDURE ReturnStatement;   
    VAR lat: Attribut;  
  BEGIN  
    IF sy = lparent THEN  
      Expression(lat);  
      Assert((blockNptr<>NIL) AND (blockNptr^.klass=funcs));  
      WITH blockNptr^.idtyp^ DO  
        Assert((form=proctypes) AND (rkind=funcs));  
        RangeCheck(funcp, lat);
        Load(lat)
      END  
    END;  
    GenBlockReturn;
  END ReturnStatement;  


  PROCEDURE Statement;   
    VAR lat: Attribut;
  BEGIN (* Statement *)  
    IF sy = becomes THEN GetSymbol; Assignment  
    ELSIF sy = call THEN GetSymbol;   
      Designator(lat); GetSymbol(*lparent*); ProcFuncCall(lat)  
    ELSIF sy = ifsy THEN GetSymbol; IfStatement  
    ELSIF sy = casesy THEN GetSymbol; CaseStatement  
    ELSIF sy = loopsy THEN GetSymbol; LoopStatement  
    ELSIF sy = whilesy THEN GetSymbol; WhileStatement  
    ELSIF sy = repeatsy THEN GetSymbol; RepeatStatement  
    ELSIF sy = withsy THEN GetSymbol; WithStatement  
    ELSIF sy = exitsy THEN GetSymbol; ExitStatement;  
    ELSIF sy = returnsy THEN GetSymbol; ReturnStatement  
    ELSIF sy = forsy THEN GetSymbol; ForStatement  
    (* ELSE empty statement without GetSymbol*)  
    END;
    (*loadCount is 0 but may be erronous because of code procedures*)
    loadCount := 0
  END Statement;  


  PROCEDURE StatSeq1(s: Symbol);    
  BEGIN  
    REPEAT 
      Statement   
    UNTIL sy = s  
  END StatSeq1;  


  PROCEDURE StatSeq3(s1, s2, s3: Symbol);   
  BEGIN  
    REPEAT
      Statement 
    UNTIL (sy = s1) OR (sy = s2) OR (sy = s3)   
  END StatSeq3;  


  PROCEDURE Block(fnptr: Idptr);
    VAR procnptr: Idptr; 
  BEGIN (* Block *)   
    WHILE (sy = proceduresy) DO 
      procnptr := nptr;
      GetSymbol;  
      INC(level);  
        Block(procnptr);  
      DEC(level)
    END;  
    blockNptr := fnptr;  
    IF sy=codesy THEN
      IF blockNptr^.externalaccess THEN 
        GenCodeBlock
      END;
      GetSymbol
    ELSE
      GenBlockEntry;
      IF sy = beginsy THEN GetSymbol;
        StatSeq1(endblock)  
      END;  
      Assert(loadCount=0);
      TerminateBlock
    END;
    Assert(sy=endblock);  
    GetSymbol (*endblock*)
  END Block;  


BEGIN  
  GetSymbol;  
  Block(NIL);  
  CloseIO
END Pass4.

