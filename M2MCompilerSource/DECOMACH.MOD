IMPLEMENTATION MODULE DecoMachineDef;  (* Ch. Jacobi *)

 
  FROM MCMnemonics IMPORT
    LIn,
    LIB,   LIW,   LID,   LLA,   LGA,   LSA,  LEA,    
    JPC,   JP,    JPFC,  JPF,   JPBC,  JPB,  ORJP, ANDJP,

    LLW,   LLD,   LEW,   LED,   LLWn,
    SLW,   SLD,   SEW,   SED,   SLWn,

    LGW,   LGD,   LGWn,
    SGW,   SGD,   SGWn,

    LSWn,
    SSWn,

    LSW,   LSD,   LSD0,  LXFW,  LSTA,  LXB,  LXW,  LXD,
    DADD,  DSUB,  DMUL,  DDIV,  DSHL,  DSHR,
    SSW,   SSD,   SSD0,  SXFW,  TS,    SXB,  SXW,  SXD,
    FADD,  FSUB,  FMUL,  FDIV,  FCMP,  FABS, FNEG, FFCT,

    READ,  WRITE, DSKR,  DSKW,  SETRK, UCHK, ESC,  SYS,           
    ENTP,  EXP,   ULSS,  ULEQ,  UGTR,  UGEQ, TRA,  RDS,
    LODFW, LODFD, STORE, STOFV, STOT,  COPT, DECS, PCOP,
    UADD,  USUB,  UMUL,  UDIV,  UMOD,  ROR,  SHL,  SHR,

    FOR1,  FOR2,  ENTC,  EXC,   TRAP,  CHK,  CHKZ, CHKS,  
    EQL,   NEQ,   LSS,   LEQ,   GTR,   GEQ,  ABSS, NEG,
    ORR,   XORR,  ANDD,  COM,   INN,   LIN,  MSK,  NOTT,
    ADD,   SUB,   MUL,   DIVV,  BIT,   NOP,  MOVF,  
     
    MOV,   CMP,   DDT,   REPL,  BBLT,  DCH,  UNPK, PACK,           
    GB,    GB1,   ALOC,  ENTR,  RTN,   CX,   CI,   CF,
    CL,    CLn;



    PROCEDURE Init1;
    BEGIN
      MnemoTab[LIn+0]  := "LI0   "; OpTab[LIn+0] := none;
      MnemoTab[LIn+1]  := "LI1   "; OpTab[LIn+1] := none;
      MnemoTab[LIn+2]  := "LI2   "; OpTab[LIn+2] := none;
      MnemoTab[LIn+3]  := "LI3   "; OpTab[LIn+3] := none;
      MnemoTab[LIn+4]  := "LI4   "; OpTab[LIn+4] := none;
      MnemoTab[LIn+5]  := "LI5   "; OpTab[LIn+5] := none;
      MnemoTab[LIn+6]  := "LI6   "; OpTab[LIn+6] := none;
      MnemoTab[LIn+7]  := "LI7   "; OpTab[LIn+7] := none;
      MnemoTab[LIn+8]  := "LI8   "; OpTab[LIn+8] := none;
      MnemoTab[LIn+9]  := "LI9   "; OpTab[LIn+9] := none;
      MnemoTab[LIn+10] := "LI10  "; OpTab[LIn+10] := none;
      MnemoTab[LIn+11] := "LI11  "; OpTab[LIn+11] := none;
      MnemoTab[LIn+12] := "LI12  "; OpTab[LIn+12] := none;
      MnemoTab[LIn+13] := "LI13  "; OpTab[LIn+13] := none;
      MnemoTab[LIn+14] := "LI14  "; OpTab[LIn+14] := none;
      MnemoTab[LIn+15] := "LI15  "; OpTab[LIn+15] := none;
  
      MnemoTab[ LIB] := "LIB   "; OpTab[ LIB] := byte;
      MnemoTab[ LIW] := "LIW   "; OpTab[ LIW] := word;
      MnemoTab[ LID] := "LID   "; OpTab[ LID] := twowords;
      MnemoTab[ LLA] := "LLA   "; OpTab[ LLA] := byte;
      MnemoTab[ LGA] := "LGA   "; OpTab[ LGA] := byte;
      MnemoTab[LSA]  := "LSA   "; OpTab[LSA] := byte;
      MnemoTab[LEA]  := "LEA   "; OpTab[LEA] := word;
      MnemoTab[JPC]  := "JPC   "; OpTab[JPC] := wordjump;
      MnemoTab[JP ]  := "JP    "; OpTab[JP ] := wordjump;
      MnemoTab[JPFC] := "JPFC  "; OpTab[JPFC] := bytejumpf;
      MnemoTab[JPF]  := "JPF   "; OpTab[JPF] := bytejumpf;
      MnemoTab[JPBC] := "JPBC  "; OpTab[JPBC] := bytejumpb;
      MnemoTab[JPB]  := "JPB   "; OpTab[JPB] := bytejumpb;
      MnemoTab[ORJP] := "ORJP  "; OpTab[ORJP] := bytejumpf;
      MnemoTab[ANDJP]:= "ANDJP "; OpTab[ANDJP]:= bytejumpf;
  
      MnemoTab[ LLW]    := "LLW   "; OpTab[ LLW] := byte;
      MnemoTab[ LLD]    := "LLD   "; OpTab[ LLD] := byte;
      MnemoTab[ LEW]    := "LEW   "; OpTab[ LEW] := word;
      MnemoTab[ LED]    := "LED   "; OpTab[ LED] := word;
      MnemoTab[LLWn+4]  := "LLW4  "; OpTab[LLWn+4] := none;
      MnemoTab[LLWn+5]  := "LLW5  "; OpTab[LLWn+5] := none;
      MnemoTab[LLWn+6]  := "LLW6  "; OpTab[LLWn+6] := none;
      MnemoTab[LLWn+7]  := "LLW7  "; OpTab[LLWn+7] := none;
      MnemoTab[LLWn+8]  := "LLW8  "; OpTab[LLWn+8] := none;
      MnemoTab[LLWn+9]  := "LLW9  "; OpTab[LLWn+9] := none;
      MnemoTab[LLWn+10] := "LLW10 "; OpTab[LLWn+10] := none;
      MnemoTab[LLWn+11] := "LLW11 "; OpTab[LLWn+11] := none;
      MnemoTab[LLWn+12] := "LLW12 "; OpTab[LLWn+12] := none;
      MnemoTab[LLWn+13] := "LLW13 "; OpTab[LLWn+13] := none;
      MnemoTab[LLWn+14] := "LLW14 "; OpTab[LLWn+14] := none;
      MnemoTab[LLWn+15] := "LLW15 "; OpTab[LLWn+15] := none;
  
      MnemoTab[SLW]     := "SLW   "; OpTab[SLW] := byte;
      MnemoTab[SLD]     := "SLD   "; OpTab[SLD] := byte;
      MnemoTab[SEW]     := "SEW   "; OpTab[SEW] := word;
      MnemoTab[SED]     := "SED   "; OpTab[SED] := word;
      MnemoTab[SLWn+4]  := "SLW4  "; OpTab[SLWn+4] := none;
      MnemoTab[SLWn+5]  := "SLW5  "; OpTab[SLWn+5] := none;
      MnemoTab[SLWn+6]  := "SLW6  "; OpTab[SLWn+6] := none;
      MnemoTab[SLWn+7]  := "SLW7  "; OpTab[SLWn+7] := none;
      MnemoTab[SLWn+8]  := "SLW8  "; OpTab[SLWn+8] := none;
      MnemoTab[SLWn+9]  := "SLW9  "; OpTab[SLWn+9] := none;
      MnemoTab[SLWn+10] := "SLW10 "; OpTab[SLWn+10] := none;
      MnemoTab[SLWn+11] := "SLW11 "; OpTab[SLWn+11] := none;
      MnemoTab[SLWn+12] := "SLW12 "; OpTab[SLWn+12] := none;
      MnemoTab[SLWn+13] := "SLW13 "; OpTab[SLWn+13] := none;
      MnemoTab[SLWn+14] := "SLW14 "; OpTab[SLWn+14] := none;
      MnemoTab[SLWn+15] := "SLW15 "; OpTab[SLWn+15] := none;
    END Init1;
 

    PROCEDURE Init2;
    BEGIN
      MnemoTab[LGW]     := "LGW   "; OpTab[LGW] := byte;
      MnemoTab[LGD]     := "LGD   "; OpTab[LGD] := byte;
      MnemoTab[LGWn+2]  := "LGW2  "; OpTab[LGWn+2] := none;
      MnemoTab[LGWn+3]  := "LGW3  "; OpTab[LGWn+3] := none;
      MnemoTab[LGWn+4]  := "LGW4  "; OpTab[LGWn+4] := none;
      MnemoTab[LGWn+5]  := "LGW5  "; OpTab[LGWn+5] := none;
      MnemoTab[LGWn+6]  := "LGW6  "; OpTab[LGWn+6] := none;
      MnemoTab[LGWn+7]  := "LGW7  "; OpTab[LGWn+7] := none;
      MnemoTab[LGWn+8]  := "LGW8  "; OpTab[LGWn+8] := none;
      MnemoTab[LGWn+9]  := "LGW9  "; OpTab[LGWn+9] := none;
      MnemoTab[LGWn+10] := "LGW10 "; OpTab[LGWn+10] := none;
      MnemoTab[LGWn+11] := "LGW11 "; OpTab[LGWn+11] := none;
      MnemoTab[LGWn+12] := "LGW12 "; OpTab[LGWn+12] := none;
      MnemoTab[LGWn+13] := "LGW13 "; OpTab[LGWn+13] := none;
      MnemoTab[LGWn+14] := "LGW14 "; OpTab[LGWn+14] := none;
      MnemoTab[LGWn+15] := "LGW15 "; OpTab[LGWn+15] := none;
  
      MnemoTab[SGW]     := "SGW   "; OpTab[SGW] := byte;
      MnemoTab[SGD]     := "SGD   "; OpTab[SGD] := byte;
      MnemoTab[SGWn+2]  := "SGW2  "; OpTab[SGWn+2] := none;
      MnemoTab[SGWn+3]  := "SGW3  "; OpTab[SGWn+3] := none;
      MnemoTab[SGWn+4]  := "SGW4  "; OpTab[SGWn+4] := none;
      MnemoTab[SGWn+5]  := "SGW5  "; OpTab[SGWn+5] := none;
      MnemoTab[SGWn+6]  := "SGW6  "; OpTab[SGWn+6] := none;
      MnemoTab[SGWn+7]  := "SGW7  "; OpTab[SGWn+7] := none;
      MnemoTab[SGWn+8]  := "SGW8  "; OpTab[SGWn+8] := none;
      MnemoTab[SGWn+9]  := "SGW9  "; OpTab[SGWn+9] := none;
      MnemoTab[SGWn+10] := "SGW10 "; OpTab[SGWn+10] := none;
      MnemoTab[SGWn+11] := "SGW11 "; OpTab[SGWn+11] := none;
      MnemoTab[SGWn+12] := "SGW12 "; OpTab[SGWn+12] := none;
      MnemoTab[SGWn+13] := "SGW13 "; OpTab[SGWn+13] := none;
      MnemoTab[SGWn+14] := "SGW14 "; OpTab[SGWn+14] := none;
      MnemoTab[SGWn+15] := "SGW15 "; OpTab[SGWn+15] := none;
  
      MnemoTab[LSWn+0]  := "LSW0  "; OpTab[LSWn+0] := none;
      MnemoTab[LSWn+1]  := "LSW1  "; OpTab[LSWn+1] := none;
      MnemoTab[LSWn+2]  := "LSW2  "; OpTab[LSWn+2] := none;
      MnemoTab[LSWn+3]  := "LSW3  "; OpTab[LSWn+3] := none;
      MnemoTab[LSWn+4]  := "LSW4  "; OpTab[LSWn+4] := none;
      MnemoTab[LSWn+5]  := "LSW5  "; OpTab[LSWn+5] := none;
      MnemoTab[LSWn+6]  := "LSW6  "; OpTab[LSWn+6] := none;
      MnemoTab[LSWn+7]  := "LSW7  "; OpTab[LSWn+7] := none;
      MnemoTab[LSWn+8]  := "LSW8  "; OpTab[LSWn+8] := none;
      MnemoTab[LSWn+9]  := "LSW9  "; OpTab[LSWn+9] := none;
      MnemoTab[LSWn+10] := "LSW10 "; OpTab[LSWn+10] := none;
      MnemoTab[LSWn+11] := "LSW11 "; OpTab[LSWn+11] := none;
      MnemoTab[LSWn+12] := "LSW12 "; OpTab[LSWn+12] := none;
      MnemoTab[LSWn+13] := "LSW13 "; OpTab[LSWn+13] := none;
      MnemoTab[LSWn+14] := "LSW14 "; OpTab[LSWn+14] := none;
      MnemoTab[LSWn+15] := "LSW15 "; OpTab[LSWn+15] := none;
  
      MnemoTab[SSWn+0]  := "SSW0  "; OpTab[SSWn+0] := none;
      MnemoTab[SSWn+1]  := "SSW1  "; OpTab[SSWn+1] := none;
      MnemoTab[SSWn+2]  := "SSW2  "; OpTab[SSWn+2] := none;
      MnemoTab[SSWn+3]  := "SSW3  "; OpTab[SSWn+3] := none;
      MnemoTab[SSWn+4]  := "SSW4  "; OpTab[SSWn+4] := none;
      MnemoTab[SSWn+5]  := "SSW5  "; OpTab[SSWn+5] := none;
      MnemoTab[SSWn+6]  := "SSW6  "; OpTab[SSWn+6] := none;
      MnemoTab[SSWn+7]  := "SSW7  "; OpTab[SSWn+7] := none;
      MnemoTab[SSWn+8]  := "SSW8  "; OpTab[SSWn+8] := none;
      MnemoTab[SSWn+9]  := "SSW9  "; OpTab[SSWn+9] := none;
      MnemoTab[SSWn+10] := "SSW10 "; OpTab[SSWn+10] := none;
      MnemoTab[SSWn+11] := "SSW11 "; OpTab[SSWn+11] := none;
      MnemoTab[SSWn+12] := "SSW12 "; OpTab[SSWn+12] := none;
      MnemoTab[SSWn+13] := "SSW13 "; OpTab[SSWn+13] := none;
      MnemoTab[SSWn+14] := "SSW14 "; OpTab[SSWn+14] := none;
      MnemoTab[SSWn+15] := "SSW15 "; OpTab[SSWn+15] := none;
    END Init2;
 
    PROCEDURE Init3;
    BEGIN
      MnemoTab[LSW]  := "LSW   "; OpTab[LSW] := byte;
      MnemoTab[LSD]  := "LSD   "; OpTab[LSD] := byte;
      MnemoTab[LSD0] := "LSD0  "; OpTab[LSD0] := none;
      MnemoTab[LXFW] := "LXFW  "; OpTab[LXFW] := none;                     
      MnemoTab[LSTA] := "LSTA  "; OpTab[LSTA] := byte;                      
      MnemoTab[LXB]  := "LXB   "; OpTab[LXB] := none;
      MnemoTab[LXW]  := "LXW   "; OpTab[LXW] := none;
      MnemoTab[LXD]  := "LXD   "; OpTab[LXD] := none;
      
      MnemoTab[DADD] := "DADD  "; OpTab[DADD] := none;
      MnemoTab[DSUB] := "DSUB  "; OpTab[DSUB] := none;
      MnemoTab[DMUL] := "DMUL  "; OpTab[DMUL] := none;   
      MnemoTab[DDIV] := "DDIV  "; OpTab[DDIV] := none;
      MnemoTab[DSHL] := "DSHL  "; OpTab[DSHL] := none;   
      MnemoTab[DSHR] := "DSHR  "; OpTab[DSHR] := none;
      
      MnemoTab[SSW]  := "SSW   "; OpTab[SSW] := byte; 
      MnemoTab[SSD]  := "SSD   "; OpTab[SSD] := byte; 
      MnemoTab[SSD0] := "SSD0  "; OpTab[SSD0] := none;    
      MnemoTab[SXFW] := "SXFW  "; OpTab[SXFW] := none;                         
      MnemoTab[TS]   := "TS    "; OpTab[TS] := none;                             
      MnemoTab[SXB]  := "SXB   "; OpTab[SXB] := none;     
      MnemoTab[SXW]  := "SXW   "; OpTab[SXW] := none;
      MnemoTab[SXD]  := "SXD   "; OpTab[SXD] := none; 
      MnemoTab[FADD] := "FADD  "; OpTab[FADD] := none;
      MnemoTab[FSUB] := "FSUB  "; OpTab[FSUB] := none;
      MnemoTab[FMUL] := "FMUL  "; OpTab[FMUL] := none;   
      MnemoTab[FDIV] := "FDIV  "; OpTab[FDIV] := none;
      MnemoTab[FCMP] := "FCMP  "; OpTab[FCMP] := none;                      
      MnemoTab[FABS] := "FABS  "; OpTab[FABS] := none;                       
      MnemoTab[FNEG] := "FNEG  "; OpTab[FNEG] := none;                    
      MnemoTab[FFCT] := "FFCT  "; OpTab[FFCT] := byte;                     

      MnemoTab[READ]  := "READ  "; OpTab[READ] := none;   
      MnemoTab[WRITE] := "WRITE "; OpTab[WRITE] := none;   
      MnemoTab[DSKR]  := "DSKR  "; OpTab[DSKR] := none;
      MnemoTab[DSKW]  := "DSKW  "; OpTab[DSKW] := none;
      MnemoTab[SETRK] := "SETRK "; OpTab[SETRK] := none;   
      MnemoTab[UCHK]  := "UCHK  "; OpTab[UCHK] := none;                         
      MnemoTab[ESC]   := "ESC   "; OpTab[ESC] := escape; 
      MnemoTab[SYS]   := "SYS   "; OpTab[SYS] := byte;

      MnemoTab[ENTP] := "ENTP  "; OpTab[ENTP] := byte;
      MnemoTab[EXP]  := "EXP   "; OpTab[EXP] := none;   
      MnemoTab[ULSS] := "ULSS  "; OpTab[ULSS] := none;
      MnemoTab[ULEQ] := "ULEQ  "; OpTab[ULEQ] := none;
      MnemoTab[UGTR] := "UGTR  "; OpTab[UGTR] := none;
      MnemoTab[UGEQ] := "UGEQ  "; OpTab[UGEQ] := none;
      MnemoTab[TRA]  := "TRA   "; OpTab[TRA] := byte;
      MnemoTab[RDS]  := "RDS   "; OpTab[RDS] := specialrds;

      MnemoTab[LODFW] := "LODFW "; OpTab[LODFW] := none;
      MnemoTab[LODFD] := "LODFD "; OpTab[LODFD] := none;
      MnemoTab[STORE] := "STORE "; OpTab[STORE] := none;
      MnemoTab[STOFV] := "STOFV "; OpTab[STOFV] := none;
      MnemoTab[STOT]  := "STOT  "; OpTab[STOT] := none;
      MnemoTab[COPT]  := "COPT  "; OpTab[COPT] := none;
      MnemoTab[DECS]  := "DECS  "; OpTab[DECS] := none;
      MnemoTab[PCOP]  := "PCOP  "; OpTab[PCOP] := byte;
      MnemoTab[UADD]  := "UADD  "; OpTab[UADD] := none;   
      MnemoTab[USUB]  := "USUB  "; OpTab[USUB] := none;   
      MnemoTab[UMUL]  := "UMUL  "; OpTab[UMUL] := none;   
      MnemoTab[UDIV]  := "UDIV  "; OpTab[UDIV] := none;   
      MnemoTab[UMOD]  := "UMOD  "; OpTab[UMOD] := none;   
      MnemoTab[ROR]   := "ROR   "; OpTab[ROR] := none;   
      MnemoTab[SHL]   := "SHL   "; OpTab[SHL] := none;
      MnemoTab[SHR]   := "SHR   "; OpTab[SHR] := none;
    END Init3;
 
    PROCEDURE Init4;
    BEGIN
      MnemoTab[FOR1] := "FOR1  "; OpTab[FOR1] := for2jump;
      MnemoTab[FOR2] := "FOR2  "; OpTab[FOR2] := for2jump;
      MnemoTab[ENTC] := "ENTC  "; OpTab[ENTC] := casejpx;
      MnemoTab[EXC]  := "EXC   "; OpTab[EXC] := none;
      MnemoTab[TRAP] := "TRAP  "; OpTab[TRAP] := none;
      MnemoTab[CHK]  := "CHK   "; OpTab[CHK] := none;
      MnemoTab[CHKZ] := "CHKZ  "; OpTab[CHKZ] := none;
      MnemoTab[CHKS] := "CHKS  "; OpTab[CHKS] := none;
      MnemoTab[EQL]  := "EQL   "; OpTab[EQL] := none;
      MnemoTab[NEQ]  := "NEQ   "; OpTab[NEQ] := none;
      MnemoTab[LSS]  := "LSS   "; OpTab[LSS] := none;
      MnemoTab[LEQ]  := "LEQ   "; OpTab[LEQ] := none;
      MnemoTab[GTR]  := "GTR   "; OpTab[GTR] := none;
      MnemoTab[GEQ]  := "GEQ   "; OpTab[GEQ] := none;
      MnemoTab[ABSS] := "ABS   "; OpTab[ABSS] := none;
      MnemoTab[NEG]  := "NEG   "; OpTab[NEG] := none;
  
      MnemoTab[ORR]  := "OR    "; OpTab[ORR] := none;
      MnemoTab[XORR] := "XOR   "; OpTab[XORR] := none;
      MnemoTab[ANDD] := "AND   "; OpTab[ANDD] := none;
      MnemoTab[COM]  := "COM   "; OpTab[COM] := none;
      MnemoTab[INN]  := "IN    "; OpTab[INN] := none;
      MnemoTab[LIN]  := "LIN   "; OpTab[LIN] := none;
      MnemoTab[MSK]  := "MSK   "; OpTab[MSK] := none;
      MnemoTab[NOTT] := "NOT   "; OpTab[NOTT] := none;
      MnemoTab[ADD]  := "ADD   "; OpTab[ADD] := none;
      MnemoTab[SUB]  := "SUB   "; OpTab[SUB] := none;
      MnemoTab[MUL]  := "MUL   "; OpTab[MUL] := none;
      MnemoTab[DIVV] := "DIV   "; OpTab[DIVV] := none;
      MnemoTab[BIT]  := "BIT   "; OpTab[BIT] := none;
      MnemoTab[NOP]  := "NOP   "; OpTab[NOP] := none;
      MnemoTab[MOVF] := "MOVF  "; OpTab[MOVF] := none;                     
  
      MnemoTab[MOV]  := "MOV   "; OpTab[MOV] := none;
      MnemoTab[CMP]  := "CMP   "; OpTab[CMP] := none;
      MnemoTab[DDT]  := "DDT   "; OpTab[DDT] := none;
      MnemoTab[REPL] := "REPL  "; OpTab[REPL] := none;
      MnemoTab[BBLT] := "BBLT  "; OpTab[BBLT] := none;
      MnemoTab[DCH]  := "DCH   "; OpTab[DCH] := none;
      MnemoTab[UNPK] := "UNPK  "; OpTab[UNPK] := none;                        
      MnemoTab[PACK] := "PACK  "; OpTab[PACK] := none;                    
      MnemoTab[GB]   := "GB    "; OpTab[GB] := byte;
      MnemoTab[GB1]  := "GB1   "; OpTab[GB1] := none;
      MnemoTab[ALOC] := "ALOC  "; OpTab[ALOC] := none;
      MnemoTab[ENTR] := "ENTR  "; OpTab[ENTR] := byte;
      MnemoTab[RTN]  := "RTN   "; OpTab[RTN] := none;
      MnemoTab[CX]   := "CX    "; OpTab[CX] := twobytes;
      MnemoTab[CI]   := "CI    "; OpTab[CI] := byte;
      MnemoTab[CF]   := "CF    "; OpTab[CF] := none;   

      MnemoTab[CL] := "CL    "; OpTab[CL] := byte;
      MnemoTab[CLn+1]  := "CL1   "; OpTab[CLn+1] := none;
      MnemoTab[CLn+2]  := "CL2   "; OpTab[CLn+2] := none;
      MnemoTab[CLn+3]  := "CL3   "; OpTab[CLn+3] := none;
      MnemoTab[CLn+4]  := "CL4   "; OpTab[CLn+4] := none;
      MnemoTab[CLn+5]  := "CL5   "; OpTab[CLn+5] := none;
      MnemoTab[CLn+6]  := "CL6   "; OpTab[CLn+6] := none;
      MnemoTab[CLn+7]  := "CL7   "; OpTab[CLn+7] := none;
      MnemoTab[CLn+8]  := "CL8   "; OpTab[CLn+8] := none;
      MnemoTab[CLn+9]  := "CL9   "; OpTab[CLn+9] := none;
      MnemoTab[CLn+10] := "CL10  "; OpTab[CLn+10] := none;
      MnemoTab[CLn+11] := "CL11  "; OpTab[CLn+11] := none;
      MnemoTab[CLn+12] := "CL12  "; OpTab[CLn+12] := none;
      MnemoTab[CLn+13] := "CL13  "; OpTab[CLn+13] := none;
      MnemoTab[CLn+14] := "CL14  "; OpTab[CLn+14] := none;
      MnemoTab[CLn+15] := "CL15  "; OpTab[CLn+15] := none;
    END Init4;

  VAR i: CARDINAL;

  BEGIN  (* initialisation of Mnemonics and Operands *)
    FOR i := 0 TO 255 DO
      MnemoTab[i] := "illeg."; OpTab[i] := illegal 
    END;
    Init1;
    Init2;
    Init3;
    Init4;
  END  DecoMachineDef.
