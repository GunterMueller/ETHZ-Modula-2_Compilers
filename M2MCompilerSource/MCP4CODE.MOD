IMPLEMENTATION MODULE MCP4CodeSys;      (* Ch. Jacobi 5.4.81; version of 10.6.81 *)

  (* $T-,R- *)

(* code generation elementary procedures 
   for Pass 4 of the Compiler for the Lilith Computer *)

  IMPORT 
    SYSTEM, Storage, MCBase, MCP4Global, MCMnemonics;
  FROM (*Terminal*) WriteStrings IMPORT 
    WriteString, WriteLn;
    (* Terminal and WriteStrings have identical 
       procedures WriteString and WriteLn!
       for medos operative system use Terminal
       for compiler transportation use WriteStrings *)


MODULE CodeSys;

  FROM SYSTEM IMPORT ADDRESS, WORD, TSIZE;
  FROM Storage IMPORT ALLOCATE, DEALLOCATE;
  FROM MCBase IMPORT
    Idptr, Stptr, Idclass, mainmodp, Varkind,
    root, globvarnext, Stringptr, stringcount;
  FROM MCP4Global IMPORT 
    MarkCodePos, WriteCodeWord, Error, Assert, loadCount;
  IMPORT PC, WriteString, WriteLn;

   EXPORT 
     (*PC,*)
     Emit, Emit2, 
     Insert, Insert2, 
     MoveCode,
     MarkShort, UpdateShort,
     MarkLong,  UpdateLong,
     LinkageMark, 
     PutConstString, InitCodeSys, 
     PutCodeText, PutCodeWord;
 
  CONST codeleng = 3500;

  TYPE  
    MarkType = (longJump, linkage);
    MarkPointer = POINTER TO MarkRecord;
    MarkRecord = 
      RECORD 
        next: MarkPointer;                     (*sequence of all marks*)
        mpc: INTEGER;                          (*this location will be remembered*)
        CASE kind: MarkType OF
          linkage:  |
          longJump: nextLongLump: MarkPointer; (*list of jumps*)
                    predecessor: MarkPointer;  (*to reeinstall list after a dispose*)
        END;
      END;

  VAR
    code: ARRAY [0..codeleng] OF CHAR;
    fixupList: MarkPointer;
    firstPossibleMark: MarkPointer; (*in current "run" of MoveCode*)
    linkFixupCount: CARDINAL;
    stringStartOffset: CARDINAL;


  PROCEDURE NewMark(VAR fmp: MarkPointer; fkind: MarkType);
  BEGIN
    IF fkind=longJump THEN NEW(fmp, longJump);
      fmp^.predecessor := NIL;
    ELSE NEW(fmp, linkage)
    END;
    WITH fmp^ DO
      next := fixupList;
      kind := fkind;
      mpc := PC;
      IF (next<>NIL) AND (next^.kind=longJump) THEN
        next^.predecessor := fmp
      END
    END;
    fixupList := fmp
  END NewMark;


  PROCEDURE DisposeLongJumpMark(m: MarkPointer);
  BEGIN
    WITH m^ DO
      Assert(kind=longJump);
      IF m=firstPossibleMark THEN firstPossibleMark := next END;
      IF predecessor<>NIL THEN predecessor^.next := next END;
      IF (next<>NIL) AND (next^.kind=longJump) THEN next^.predecessor := predecessor END;
      IF m=fixupList THEN fixupList := next END
    END;
    DISPOSE(m, longJump)
  END DisposeLongJumpMark;
 

  PROCEDURE Emit(i: WORD);
  BEGIN
    code[PC] := CHAR(i); INC(PC); 
    IF PC>codeleng THEN CodeOverflow END
  END Emit;


  PROCEDURE Emit2(i: WORD);
  BEGIN
    code[PC] := CHAR(CARDINAL(i) DIV 400B); INC(PC); 
    IF PC>=codeleng THEN CodeOverflow END;
    code[PC] := CHAR(CARDINAL(i) MOD 400B); INC(PC)
  END Emit2;
   

  PROCEDURE Insert(at: CARDINAL; i: WORD);
  BEGIN
    code[at]   := CHAR(i)
  END Insert;


  PROCEDURE Insert2(at: CARDINAL; i: WORD);
  BEGIN
    code[at]   := CHAR(CARDINAL(i) DIV 400B);
    code[at+1] := CHAR(CARDINAL(i) MOD 400B)
  END Insert2;
   

  PROCEDURE MoveMarks(from, to, displacement: CARDINAL);
  BEGIN
    LOOP
      IF firstPossibleMark=NIL THEN EXIT END;
      WITH firstPossibleMark^ DO
        IF ORD(mpc)<from THEN EXIT END; 
        IF ORD(mpc)<=to THEN INC(mpc, displacement) END;
        firstPossibleMark := firstPossibleMark^.next 
      END
    END
  END MoveMarks;
   

  PROCEDURE MoveCode(from, to, displacement: CARDINAL);
    (* from:  start of moving area
       to:    end of moving area
       displacement: moving distance
       - a run is a sequence of calls of MoveCode;
       - if to points to current instructioncount then PC is updated 
          and a new run starts;
          <> the first MoveCode of any run has "to" pointing to PC
              [otherwise firstPossibleMark is not initialized...]
       - successive calls of MoveCode in the same run
         must have decreasing from parameter values; and must not
         overlap *)
    VAR l: INTEGER;
  BEGIN
    Assert(to>from);
    IF to+1 = ORD(PC) THEN PC := to+1+displacement;
      IF PC>=codeleng THEN CodeOverflow; RETURN END;
      firstPossibleMark := fixupList
    END;
    FOR l := to TO from BY -1 DO code[ORD(l)+displacement] := code[l] END;
    MoveMarks(from, to, displacement)
  END MoveCode;
   

  PROCEDURE MarkLong(VAR root: INTEGER);
    (* insert a long jump in a linear list. *)
    VAR lp: MarkPointer;
  BEGIN 
    NewMark(lp, longJump);
    WITH lp^ DO
      nextLongLump := MarkPointer(root)
    END;
    Emit2(0);     
    root := INTEGER(lp)
  END MarkLong;
  

  PROCEDURE UpdateLong(root: INTEGER);
    (* Update list of long jumps *) 
    VAR lp, oldlp: MarkPointer;
  BEGIN lp:= MarkPointer(root);
    WHILE (lp<>NIL) AND (CARDINAL(lp)<>0) DO
      oldlp := lp;
      WITH oldlp^ DO
        Assert(kind=longJump);
        Insert2(mpc, PC-mpc);
        lp := nextLongLump
      END;
      DisposeLongJumpMark(oldlp);
    END
  END UpdateLong;
  

  PROCEDURE MarkShort(VAR lastPC: INTEGER);
    (* insert a short jump in a list *)
  BEGIN   
    IF lastPC=0 THEN (* list is empty *)
      Emit(0);     
    ELSIF ORD(PC-lastPC)>255 THEN 
      Error(203); Emit(0)   
    ELSE
      Emit(PC-lastPC)
    END;
    lastPC := PC-1
  END MarkShort;
  

  PROCEDURE UpdateShort(lastPC: INTEGER); 
    (* Update list of short jumps *)
    VAR nextOffset: INTEGER;
  BEGIN
    WHILE lastPC<>0 DO
      Assert((PC-lastPC)<256);
      nextOffset := INTEGER(code[lastPC]);
      code[lastPC] := CHAR(PC-lastPC);
      IF nextOffset<>0 THEN 
        lastPC := lastPC-nextOffset 
      ELSE 
        lastPC := 0 
      END
    END
  END UpdateShort;


  PROCEDURE LinkageMark;
    (* remember PC for later fixups *)
    VAR lp: MarkPointer;
  BEGIN
    NewMark(lp, linkage);
    INC(linkFixupCount)
  END LinkageMark;


  (* loader format table entries *)
  CONST
    xVERSION  = 200B;
    xMODULE   = 201B;
    xIMPORT   = 202B;
    xCODETEXT = 203B;
    xDATATEXT = 204B;
    xFIXUP    = 205B;


  PROCEDURE PutConstString(stringTypePtr: Stptr; string: Stringptr);
    (* Determine if string has already been generated,
       else generate template of string *)
    TYPE StringTemplatePtr = POINTER TO ARRAY [0..120] OF CHAR;(*pass 1 !*)
    VAR l, c: CARDINAL;
        stp: StringTemplatePtr;
  BEGIN
    WITH string^ DO
      IF valentry<>CARDINAL(NIL) THEN
        (* generate a template *)
        WriteCodeWord(xDATATEXT);
        (* Size of string including at least 1 OC Char *)
        l := (stringTypePtr^.ixp^.max+3) DIV 2;
        WriteCodeWord(l+1); (* FrameSize *)
        WriteCodeWord(loadoffset+stringStartOffset);
        stp := StringTemplatePtr(valentry);
        FOR c := 1 TO l DO
          WriteCodeWord(CARDINAL(stp^[c*2-2])*400B+CARDINAL(stp^[c*2-1]));
        END;
        valentry := CARDINAL(NIL)
      END
    END
  END PutConstString;


  PROCEDURE PutCodeText(loadAddress: CARDINAL);
    (* Put the Code of a Procedure to the Linker File *)
    VAR l, wpc: INTEGER;

    PROCEDURE LinkageUpdate(ProcAddr: INTEGER);
      VAR lp: MarkPointer;
    BEGIN
      (* now only Correct Module Number exists *)
      IF linkFixupCount>0 THEN
        WriteCodeWord(xFIXUP);
        WriteCodeWord(linkFixupCount);
        WHILE fixupList<>NIL DO
          WITH fixupList^ DO
            Assert(kind=linkage);
            WriteCodeWord(mpc+ProcAddr);
            lp := fixupList; fixupList := next
          END;
          DISPOSE(lp, linkage)
        END
      END;
      linkFixupCount := 0;
      fixupList := NIL
    END LinkageUpdate;
  
  BEGIN
    Assert(NOT ODD(PC));           
    wpc := PC DIV 2;
    WriteCodeWord(xCODETEXT);
    WriteCodeWord(wpc+1);
    WriteCodeWord(loadAddress);
    FOR l := 1 TO wpc DO
      WriteCodeWord(CARDINAL(code[2*l-2])*400B+CARDINAL(code[2*l-1]))
    END;
    LinkageUpdate(2*loadAddress)
  END PutCodeText;
  

  PROCEDURE PutCodeWord(loadAddress, value: CARDINAL);
    (* addr is Word-address of storage word *)
  BEGIN
    WriteCodeWord(xCODETEXT);
    WriteCodeWord(2);
    WriteCodeWord(loadAddress);
    WriteCodeWord(value)
  END PutCodeWord;


  PROCEDURE Sum(a, b: CARDINAL): CARDINAL;
  BEGIN
    IF b>177777B-a THEN 
      Error(201); a := 0 
    END;
    RETURN a+b  
  END Sum;


  PROCEDURE InitOffsets;
   (* determines Size for globalMod Variables *)
    VAR lp: Idptr; sze: CARDINAL;
  BEGIN
    sze := 0;
    lp := mainmodp^.globvarp;
    WHILE lp<>NIL DO
      WITH lp^ DO
        Assert((klass=vars) AND (vkind=noparam));
        IF indaccess THEN
          sze := Sum(sze, idtyp^.size)
        END;
        lp := vlink 
      END
    END;
    stringStartOffset := Sum(sze, globvarnext)
  END InitOffsets;


  PROCEDURE ModuleInitialisation;
  
    PROCEDURE PutInitialisationFlag;
      (* Initialisation Flag and pointer to the Start of
         the Constant String Area *)
    BEGIN
      (* Flag <> 0 determines Module is Initialized *)
      WriteCodeWord(xDATATEXT);
      WriteCodeWord(3); (* FrameSize *)
      WriteCodeWord(1); (* Address of Flag *)
      WriteCodeWord(0); (* Contents, means not initialized *)
      WriteCodeWord(0)  (* Pointer to String Constants *)
    END PutInitialisationFlag;
  
    PROCEDURE PutImports;
      (* Linker Directive to connect 
         local Module Numbers to Names *)
      VAR lp, lp1: Idptr; i, count: INTEGER;
    BEGIN
      lp := root^.locp^.link;
      (* first determine Number of Modules *)
      lp1 := lp; count := 0;
      WHILE lp1<>NIL DO
        Assert(lp1^.globalmodule);
        INC(count);
        lp1 := lp1^.link
      END;
      WriteCodeWord(xIMPORT);
      WriteCodeWord(CARDINAL(count)*11); (* framesize *)
      FOR i := 1 TO count DO
        (* find Module No i *)
        lp1 := lp;
        LOOP
          (* at least mainmodp *)
          Assert(lp1<>NIL);
          IF INTEGER(lp1^.modnum)=i THEN EXIT END;
          lp1 := lp1^.link
        END;
        PutModuleName(lp1)
      END
    END PutImports;
  
    PROCEDURE PutModuleName(modP: Idptr);
      (* Puts Name and Key of Module Modp^ to the Linker File *)
      VAR i: INTEGER;
    BEGIN
      Assert(modP<>NIL);
      WITH modP^ DO
        Assert((klass=mods) AND globalmodule);
        FOR i := 0 TO 15 BY 2 DO
          WriteCodeWord(
          CARDINAL(identifier[i])*400B+CARDINAL(identifier[i+1]));
        END;
        WriteCodeWord(modulekey[0]);
        WriteCodeWord(modulekey[1]);
        WriteCodeWord(modulekey[2])
      END
    END PutModuleName;

    PROCEDURE PutModuleHeader(dataSize: CARDINAL);
      VAR l: INTEGER;
    BEGIN
      WriteCodeWord(xVERSION);
      WriteCodeWord(1);        (*framesize*)
      WriteCodeWord(3);        (*versionkey*)
      MarkCodePos;
      WriteCodeWord(xMODULE);
      WriteCodeWord(12);       (*framesize*)
      PutModuleName(mainmodp);
      WriteCodeWord(dataSize)
    END PutModuleHeader;
  
  BEGIN (*ModuleInitialisation*)
    PutModuleHeader(stringStartOffset+stringcount);
    PutImports;
    PutInitialisationFlag
  END ModuleInitialisation;


  PROCEDURE CodeOverflow;
    VAR c: CARDINAL; lp: MarkPointer;
  BEGIN
    (* for transportation of the compiler don't worry that procedure;
       replace its body by HALT *)
    WriteString(" ---- code overflow"); WriteLn;
    Error(205);
    firstPossibleMark := NIL; linkFixupCount := 0;
    (*denote shortjumps to update correctly*)
    FOR c := 0 TO 256 DO code[c] := code[codeleng-256+c] END;
    FOR c := 257 TO codeleng DO code[c] := CHAR(0) END;
    PC := 257;
    (*denote marked jumps to update correctly;
      set link fields to NIL but don't dispose elements*)
    c := 0;
    WHILE fixupList<>NIL DO
      lp := fixupList;
      WITH lp^ DO
        fixupList := next;
        next := NIL;
        c := c+2; mpc := c; (*prevents arithmtic overflow*)
        IF kind=longJump THEN nextLongLump := NIL; predecessor := NIL END
      END
    END; 
    (*HALT*)
  END CodeOverflow;


  PROCEDURE InitCodeSys;
    (*because of exporting PC the module needs explicite initialization*)
  BEGIN (* InitCodeSys *)  
    fixupList := NIL;
    linkFixupCount := 0;
    PC := 0;
    InitOffsets;
    ModuleInitialisation
  END InitCodeSys;

END CodeSys;

 
MODULE SimpleCode;

  FROM MCP4Global IMPORT 
    Error, Assert, loadCount, CompilerError;
  IMPORT CodeSys, PC;
         
  FROM MCMnemonics IMPORT   
    LIn,  LIN,
    LIB,  LIW,  LGA,  LSA,           
    JPFC, 
    LLW,  SLW,  
    LGW,  SGW,    
    LSW,  SSW, LSWn, SSWn,
    COPT,
    ADD,  SUB,  UADD, UMUL, UDIV, UMOD,
    XORR, ANDD, SHL,  SHR, 
    CL,   CLn;
     

  EXPORT 
    Emit2GivePC, Fixup2,
    EmitPacked, EmitLI, EmitLSW,
    EmitSSW, EmitCL, UAddToTop, IAddToTop, UConstMul, 
    UConstDiv, UConstMod;


  PROCEDURE Emit2GivePC(VAR fPC: INTEGER); 
    (* if code is moved no trackkeeping is done *)
  BEGIN
    fPC := PC;
    Emit2(0);
  END Emit2GivePC;


  PROCEDURE Fixup2(fPC: INTEGER);
    (* long jump at fPC jumps to PC *)
  BEGIN 
    Insert2(fPC, PC-fPC)
  END Fixup2;


  PROCEDURE EmitPacked(op, f: CARDINAL);  
    VAR short: BOOLEAN;
  BEGIN 
    IF (op=LLW) OR (op=SLW) THEN
      short := (f>3) AND (f<16)  
    ELSIF (op=LGW) OR (op=SGW) THEN 
      short := (f>1) AND (f<16)  
    ELSE
      short := FALSE   
    END; 
    Assert(f<256);
    IF short THEN Emit(op+f)                                                    
    ELSE Emit(op); Emit(f) 
    END
  END EmitPacked; 


  PROCEDURE EmitLI(i: CARDINAL);
  BEGIN
    IF i<16 THEN Emit(LIn+i)
    ELSIF i<256 THEN Emit(LIB); Emit(i)
    ELSIF i=177777B THEN Emit(LIN)
    ELSE Emit(LIW); Emit2(i)
    END;
    IF loadCount>15 THEN Error(204) END;
    INC(loadCount)
  END EmitLI;

  
  PROCEDURE EmitLSW(i: CARDINAL);
  BEGIN
    IF i<16 THEN Emit(LSWn+i)
    ELSIF i<256 THEN Emit(LSW); Emit(i)
    ELSE 
      UAddToTop(i); Emit(LSWn)
    END
  END EmitLSW;

 
  PROCEDURE EmitSSW(i: CARDINAL);
  BEGIN 
    IF i<16 THEN Emit(SSWn+i);
    ELSIF i<256 THEN Emit(SSW); Emit(i)
    ELSE CompilerError
    END;
    DEC(loadCount, 2)
  END EmitSSW;

  
  PROCEDURE EmitCL(i: CARDINAL);
  BEGIN
    IF (i<=15) AND (i<>0) THEN Emit(CLn+i)
    ELSE Emit(CL); Emit(i) 
    END
  END EmitCL;


  PROCEDURE UAddToTop(x: CARDINAL);
    (* address arithmetic intended!;
       x positive, no wraparound allowed,
        may generate either LSA or UADD instructions*)
  BEGIN
    IF x>0 THEN
      IF x<=255 THEN Emit(LSA); Emit(x)
      ELSE EmitLI(x); Emit(UADD); DEC(loadCount)
      END
    END
  END UAddToTop;


  PROCEDURE IAddToTop(x: INTEGER);
    (* generates code to increment the value on top of stack,
       integer arithmetic *)
  BEGIN
    IF x<>0 THEN
      IF x<0 THEN  
        EmitLI(ORD(-x)); Emit(SUB); 
      ELSE
        EmitLI(x); Emit(ADD)
      END;
      DEC(loadCount)
    END
  END IAddToTop;


  PROCEDURE UConstMul(c: CARDINAL);
    (* multiplies top value by c, unsigned arithmetic *)
    VAR mask, power: CARDINAL;
  BEGIN
    IF c<>1 THEN
      IF c=0 THEN Emit(COPT); Emit(XORR)
      ELSIF c=2 THEN Emit(COPT); Emit(UADD)
      ELSE  mask := 4; power := 2;
        LOOP
          IF mask=c THEN EmitLI(power); Emit(SHL); EXIT END;
          IF power=15 THEN EmitLI(c); Emit(UMUL); EXIT END;
          mask := 2*mask; INC(power)
        END;
        DEC(loadCount)
      END
    END
  END UConstMul;


  PROCEDURE UConstDiv(c: CARDINAL);
    (* divides top element by c, unsigned arithmetic *)
    VAR mask, power: CARDINAL;
  BEGIN
    IF c<>1 THEN
      IF c=0 THEN Error(221)
      ELSE mask := 2; power := 1;
        LOOP
          IF c=mask THEN EmitLI(power); Emit(SHR); EXIT END;
          IF power=15 THEN EmitLI(c); Emit(UDIV); EXIT END;
          INC(power); mask := 2*mask
        END;
        DEC(loadCount)
      END
    END
  END UConstDiv;


  PROCEDURE UConstMod(c: CARDINAL);
    (* take modulus of top element, unsigned arithmetic *)
    VAR mask: CARDINAL;
  BEGIN  mask := 177777B;
    IF c=0 THEN Error(221) 
    ELSE 
      LOOP
        IF (c-1)=mask THEN EmitLI(mask); Emit(ANDD); EXIT END;
        IF mask=0 THEN EmitLI(c); Emit(UMOD); EXIT END;
        mask := mask DIV 2
      END;
      DEC(loadCount)
    END
  END UConstMod;


END SimpleCode;


MODULE TypeSystem;
  FROM MCBase IMPORT Stptr, charptr, Structform;
  EXPORT IsArrayType, ByteSize, IsSetType;


  PROCEDURE ByteSize(fsp: Stptr): BOOLEAN;   
  BEGIN   
    RETURN (fsp=charptr) OR 
              (fsp^.form=subranges) AND (fsp^.scalp=charptr)
  END ByteSize;  


  PROCEDURE IsSetType(fsp:Stptr): BOOLEAN;   
  BEGIN   
    RETURN fsp^.form=sets  
  END IsSetType;  


  PROCEDURE IsArrayType(fsp:Stptr): BOOLEAN;   
  BEGIN   
    RETURN fsp^.form=arrays  
  END IsArrayType;  


END TypeSystem;


MODULE BlockSystem;
  IMPORT 
    CodeSys, SimpleCode, TypeSystem, PC;
  FROM MCBase IMPORT
    Idptr, Stptr, mainmodp, Varkind, Structform,
    charptr, globvarnext, root, Idclass, noprio;
  FROM MCP4Global IMPORT 
    blockNptr, 
    loadAddress, loadCount, (*PC,*) CompilerError, Assert; 
  FROM MCMnemonics IMPORT   
    LIn,
    LIB,  LIW,  LGA, LSA,  
    JPFC, TRAP, NOP,
    LLD,  
    SLW,  SLD,  
    LGW,  SGW,  SGD,   
    ENTR, ALOC, 
    COPT, DECS, PCOP,
    ENTP, EXP,
    SHR,  
    RTN,  CX,   CI,  CF, TS;
     
  EXPORT 
    GenBlockEntry, GenBlockReturn, TerminateBlock,
    CodeBody, GenCodeBlock;
  

  PROCEDURE GenBlockEntry;
    (* fix proceduretable and generate entry sequence *)
    VAR lvp, lpp, lpp1: Idptr;
        n, i, l: CARDINAL;
  BEGIN loadCount := 0; PC := 0;
    IF blockNptr<>NIL THEN
      WITH blockNptr^ DO
        PutCodeWord(procnum, 2*loadAddress); (* Fix ProcedureTable *)
        Emit(ENTR); Emit(varlength-4); (*>= 4 local vars !*)
        IF blockNptr=mainmodp THEN
          (* Test and return if already initialized *)
            EmitPacked(LGA, 1);
            Emit(TS);
            Emit(JPFC); Emit(2);
            Emit(RTN);
          (* globalMod variables *)        
            Assert(globvarnext<=400B);
            Emit(LGA); Emit(globvarnext); (*future ptr to string templates; stored later*)
            lvp := globvarp;
            WHILE lvp<>NIL DO
              WITH lvp^ DO
                Assert((klass=vars) AND (vkind=noparam));
                IF indaccess THEN
                  Emit(COPT); EmitPacked(SGW, vaddr);
                  UAddToTop(idtyp^.size);
                END;
                lvp := vlink
              END
            END; 
            EmitPacked(SGW, 2); (*stores pointer to string templates*)
          (* Call the Initialisations of Imported modules *)
            lpp := root^.locp^.link;
            WHILE lpp<>NIL DO
              IF lpp<>mainmodp THEN
                Assert(lpp^.globalmodule);
                Emit(CX); LinkageMark; Emit(lpp^.modnum);
                Emit(0); (* Procedure Number for Initialisation *)
              END;
              lpp := lpp^.link
            END;
          (* There are no parameters *)
            lpp := NIL;
        ELSIF blockNptr^.klass=mods THEN
          lpp := NIL; lvp := NIL
        ELSE lvp := locvarp;
          lpp := idtyp^.fstparam
        END
      END;
      (* save first parameter to allow interrupts *)
      (* reverse order, but no change of link since parameter are 
         used before and after this peace of code *)
      n := 0; lpp1 := lpp;
      WHILE lpp<>NIL DO INC(n); lpp := lpp^.vlink END;
      FOR i := n TO 1 BY -1 DO
        lpp := lpp1;
        FOR l := 2 TO i DO lpp := lpp^.vlink END;
        WITH lpp^ DO
          Assert(klass=vars); 
          CASE vkind OF
            noparam:  CompilerError
          | varparam:                             
              IF IsArrayType(idtyp) AND idtyp^.dyn THEN
                Emit(SLD); Emit(vaddr)
              ELSE
                EmitPacked(SLW, vaddr)
              END
          | valparam:
              IF idtyp^.size=1 THEN EmitPacked(SLW, vaddr)
              ELSE 
                Assert(idtyp^.size=2); 
                Emit(SLD); Emit(vaddr)
              END
          | copyparam:
              IF IsArrayType(idtyp) AND idtyp^.dyn THEN
                Emit(SLD); Emit(vaddr);
                Emit(LLD); Emit(vaddr);
                IF ByteSize(idtyp^.elp) THEN
                  EmitLI(1); Emit(SHR); DEC(loadCount);
                  Emit(LSA); Emit(1)
                ELSE
                  Emit(LSA); Emit(1); UConstMul(idtyp^.elp^.size)
                END
              ELSE
                Assert(indaccess);
                EmitLI(idtyp^.size); DEC(loadCount)
              END;
              Emit(PCOP); Emit(vaddr)
          END
        END (*With*)
      END; (*FOR*)
      (* allocate space for local variables *)
      WHILE lvp<>NIL DO  
        WITH lvp^ DO
          Assert((klass=vars) AND (vkind=noparam));
          IF indaccess THEN      
            EmitLI(idtyp^.size); DEC(loadCount);
            Emit(ALOC);
            EmitPacked(SLW, vaddr)
          END;
          lvp := vlink
        END
      END;
      IF (blockNptr^.priolev<>noprio) AND blockNptr^.externalaccess THEN
        Emit(ENTP);
        Emit(blockNptr^.priolev+1)
      END
    END;
    loadCount := 0;
  END GenBlockEntry;


  PROCEDURE GenBlockReturn;
    (* generate a return from a block *)
  BEGIN
    IF (blockNptr^.priolev<>noprio) AND blockNptr^.externalaccess THEN
      Emit(EXP)
    END;
    Emit(RTN);
    loadCount := 0
  END GenBlockReturn;


  PROCEDURE TerminateBlock;
    (* generate exit sequence and 
       terminates handling of the current block*)
  BEGIN
    IF blockNptr<>NIL THEN
      IF blockNptr^.klass=funcs THEN
        EmitLI(9); Emit(TRAP)
      ELSE 
        GenBlockReturn 
      END;
      IF ODD(PC) THEN Emit(NOP) END;
      PutCodeText(loadAddress);
      INC(loadAddress, PC DIV 2); 
      PC := 0
    END;
    loadCount := 0
  END TerminateBlock;


  PROCEDURE CodeBody(fpptr: Idptr);
    (* inline body of CODE procedure *)
    TYPE CodePtr = POINTER TO ARRAY [0..77777B] OF CARDINAL;
    VAR i: CARDINAL; cptr: CodePtr;
  BEGIN  
    WITH fpptr^ DO
      cptr := CodePtr(codeentry);
      i := 0;
      WHILE i<codelength DO 
        Emit(cptr^[i]); INC(i)
      END
    END
  END CodeBody;


  PROCEDURE GenCodeBlock;
    (* complete non-inline CODE procedure *)
  BEGIN
    PC := 0;
    WITH blockNptr^ DO
      PutCodeWord(procnum, 2*loadAddress) (* Fix ProcedureTable *)
    END;
    IF (blockNptr^.priolev<>noprio) THEN (*allways externalaccess*)
      Emit(ENTP);
      Emit(blockNptr^.priolev+1)
    END;
    CodeBody(blockNptr);
    (* TerminateBlock would generate TRAP instead of RTN *)
    GenBlockReturn;
    IF ODD(PC) THEN Emit(NOP) END;
    PutCodeText(loadAddress);
    INC(loadAddress, PC DIV 2);
    loadCount := 0
  END GenCodeBlock;


END BlockSystem;


END MCP4CodeSys.

