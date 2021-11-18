MODULE decode;   (*NW 26.1.84*)
  FROM InOut IMPORT Done,
    OpenInput, OpenOutput, CloseInput, CloseOutput,
    Read, ReadWrd,
    Write, WriteLn, WriteString, WriteCard, WriteOct;

  TYPE String = ARRAY [0..63] OF CHAR;

  VAR ch: CHAR; a, L, w: CARDINAL;
    Mnem: ARRAY [0..15] OF String;

  PROCEDURE Rd(n: CARDINAL);
  BEGIN ReadWrd(w); IF w # n THEN HALT END
  END Rd;

  PROCEDURE ReadName;
    VAR i: CARDINAL;
  BEGIN Write(" "); Write(" ");
    FOR i := 0 TO 15 DO Read(ch);
      IF ch < " " THEN ch := " " END ;
      Write(ch)
    END ;
    WriteString("    key =");
    FOR i := 0 TO 2 DO ReadWrd(w); WriteOct(w, 7) END ;
    WriteLn
  END ReadName;

  PROCEDURE WBt;
    VAR cch: CHAR;
  BEGIN Read(cch); a := a+1;
    WriteString("   "); WriteOct(CARDINAL(cch), 3)
  END WBt;

  PROCEDURE WWd;
    VAR cch, cch1: CHAR;
  BEGIN Read(cch); Read(cch1); a := a+2;
    WriteOct(CARDINAL(cch)*400B + CARDINAL(cch1), 9)
  END WWd;

  PROCEDURE WOp(n: CARDINAL);
    VAR i,j: CARDINAL;
  BEGIN i := n DIV 20B; j := (n MOD 20B) * 4;
    Write(Mnem[i,j]); Write(Mnem[i,j+1]); Write(Mnem[i,j+2]); ch := Mnem[i,j+3];
    IF    ch = "+" THEN WBt
    ELSIF ch > "`" THEN WriteCard(CARDINAL(ch) - 87, 2)
    ELSIF ch = "-" THEN WBt; WBt
    ELSIF ch = "*" THEN WWd
    ELSIF ch = "/" THEN WWd; WWd
    ELSIF ch = "?" THEN WBt; WWd
    ELSE Write(ch)
    END
  END WOp;

BEGIN
  Mnem[ 0] := "LI0 LI1 LI2 LI3 LI4 LI5 LI6 LI7 LI8 LI9 LI10LI11LI12LI13LI14LI15";
  Mnem[ 1] := "LIB+--- LIW*LID/LLA+LGA+LSA+LEA*JPC*JP *JFC+JPF+JBC+JPB+ORJ+AJP+";
  Mnem[ 2] := "LLW+LLD+LEW-LED-LLW4LLW5LLW6LLW7LLW8LLW9LLWaLLWbLLWcLLWdLLWeLLWf";
  Mnem[ 3] := "SLW+SLD+SEW-SED-SLW4SLW5SLW6SLW7SLW8SLW9SLWaSLWbSLWcSLWdSLWeSLWf";
  Mnem[ 4] := "LGW+LGD+LGW2LGW3LGW4LGW5LGW6LGW7LGW8LGW9LGWaLGWbLGWcLGWdLGWeLGWf";
  Mnem[ 5] := "SGW+SGD+SGW2SGW3SGW4SGW5SGW6SGW7SGW8SGW9SGWaSGWbSGWcSGWdSGWeSGWf";
  Mnem[ 6] := "LSW0LSW1LSW2LSW3LSW4LSW5LSW6LSW7LSW8LSW9LSWaLSWbLSWcLSWdLSWeLSWf";
  Mnem[ 7] := "SSW0SSW1SSW2SSW3SSW4SSW5SSW6SSW7SSW8SSW9SSWaSSWbSSWcSSWdSSWeSSWf";
  Mnem[ 8] := "LSW+LSD+LSD0LXFWLST+LXB LXW LXD DADDDSUBDMULDDIV--- --- DSHLDSHR";
  Mnem[ 9] := "SSW+SSD+SSD0SXFWTS  SXB SXW SXD FADDFSUBFMULFDIVFCMPFABSFNEGFCT+";
  Mnem[10] := "READWRT DSKRDSKWSTRKUCHK--- SYS+ENP+EXP ULSSULEQUGTRUGEQTRA+RDS+";
  Mnem[11] := "LDFWLDFDSTORSTFVSTOTCOPTDECSPCP+UADDUSUBUMULUDIVUMODROR SHL SHR ";
  Mnem[12] := "FR1?FR2?ENC*EXC TRAPCHK CHKZCHKSEQL NEQ ILSSILEQIGTRIGEQABS NEG ";
  Mnem[13] := "OR  XOR AND COM IN  LIN MSK NOT IADDISUBIMULIDIV--- BIT NOP MOVF";
  Mnem[14] := "MOV CMP DDT REPLBBLTDCH UNPKPACKGB +GB1 ALOCENT+RTN CLX-CLI+CLF ";
  Mnem[15] := "CLL+CLL1CLL2CLL3CLL4CLL5CLL6CLL7CLL8CLL9CLLaCLLbCLLcCLLdCLLeCLLf";

  LOOP OpenInput("OBJ");
    IF NOT Done THEN EXIT END ;
    OpenOutput("DEX");
    IF NOT Done THEN Write(14C) END ;
    Rd(200B); Rd(1); ReadWrd(w);
    Rd(201B); Rd(14); WriteString("header"); WriteLn; ReadName;
    ReadWrd(w); WriteString("  datasize ="); WriteOct(w,7);
    ReadWrd(w); WriteString("   codesize ="); WriteOct(w,7);
    ReadWrd(w); WriteLn; ReadWrd(w);
    IF w = 202B THEN
        ReadWrd(L); WriteString("imports: "); WriteLn;
        WHILE L > 0 DO ReadName; L := L-11 END ;
        ReadWrd(w)
    END ;
    WHILE w = 204B DO
        WriteLn; ReadWrd(L);
        ReadWrd(a); WriteString("data"); WriteLn;
        WHILE L > 1 DO
          WriteOct(a, 8); a := a+1; ReadWrd(w);
          WriteOct(w, 8); WriteLn; L := L-1
        END ;
        ReadWrd(w)
    END ;
    IF w = 203B THEN
        WriteLn; ReadWrd(L); Rd(0); WriteString("entries"); a := 0; WriteLn;
        WHILE L > 1 DO
          WriteOct(a, 8); a := a+2; ReadWrd(w);
          WriteOct(w, 8); WriteLn; L := L-1
        END ;
        ReadWrd(w)
    END ;
    IF w = 203B THEN
        WriteLn; ReadWrd(L); ReadWrd(a); WriteString("code"); WriteLn;
        L := 2*(a+L-1); a := 2*a;
        WHILE a < L DO
          WriteOct(a, 8); a := a+1; Read(ch); w := CARDINAL(ch);
          WriteString("  "); WOp(w); WriteLn
        END ;
        ReadWrd(w)
    END ;
    IF w = 205B THEN
        WriteLn; ReadWrd(L); WriteString("relocation"); WriteLn;
        WHILE L > 0 DO
          ReadWrd(w); WriteOct(w, 8); WriteLn; L := L-1
        END
    END ;
    CloseOutput; CloseInput
  END
END decode.
