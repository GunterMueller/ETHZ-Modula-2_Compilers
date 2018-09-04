(****************************************
*                                       *
*     MODULA-2 Multi-Pass Compiler      *
*     ****************************      *
*                                       *
*     Implementation for Lilith         *
*                                       *
*                                       *
*     MCP1Reals:                        *
*                                       * 
*     Real constant handling in Pass 1  *
*                                       * 
*     Version C18 of 05.03.81           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

IMPLEMENTATION MODULE MCP1Reals;  (* LG *)

  (* $T-,R- *)

  FROM Storage IMPORT ALLOCATE;
  FROM MCBase IMPORT Constval; 
 
  (* (* definitions in definition module *)
  EXPORT QUALIFIED
    InitRealConst, ConvertToFraction, ConvertToExponent, TermRealConst;
  (* end definitions *) *)
 
  CONST maxexp = 39;
        minexp = -38;
        maxdignum = 7;
        maxfractdigits = "17014118"; (* first decimal digits of 2**127 *)
 
  TYPE String10 = ARRAY[0..9] OF CHAR;
 
  VAR maxfract : REAL;
      r0, r1, r10 : REAL; 
      rval : REAL;
      base : REAL;
      period : BOOLEAN;
      exp : INTEGER;
      dignum : INTEGER;
      eval : INTEGER;
      eok : BOOLEAN;
      negexp : BOOLEAN;
 
  PROCEDURE Float(int: CARDINAL): REAL;
    (* simulation of float function for numbers 0 .. 10 *)

    VAR
      conv : RECORD
               rh, rl : CARDINAL;
             END;

  BEGIN (* Float *)
    WITH conv DO
      rl := 0;
      CASE int OF
        0 : rh := 00000B;
      | 1 : rh := 40200B;
      | 2 : rh := 40400B;
      | 3 : rh := 40500B;
      | 4 : rh := 40600B;
      | 5 : rh := 40640B;
      | 6 : rh := 40700B;
      | 7 : rh := 40740B;
      | 8 : rh := 41000B;
      | 9 : rh := 41020B;
      | 10 : rh := 41040B;
      ELSE HALT;
      END; (* CASE *)
    END; (* WITH *)
    RETURN REAL(conv);
  END Float;

  PROCEDURE InitRealConst;
    (* initialise the calculation of a constant real number *)
  BEGIN
    rval := r0;
    base := r1;
    period := FALSE;
    exp := 0;
    dignum := 0;
    eval := 0;
    eok := TRUE;
    negexp := FALSE;
  END InitRealConst;
 
  PROCEDURE ConvertToFraction(ch: CHAR);
    (* convert a character to the fraction of a constant real number *)
  BEGIN
    IF ch = '.' THEN period := TRUE;
    ELSE
      IF (dignum = 0) AND (ch = '0') THEN
        IF period THEN DEC(exp) END;
      ELSIF dignum < maxdignum THEN 
        rval := rval * r10 + Float(ORD(ch) - ORD('0')); 
        IF period THEN DEC(exp) END; 
        INC(dignum); 
      ELSE
        base := base / r10;
        rval := rval + base * Float(ORD(ch) - ORD('0'));
        IF NOT period THEN INC(exp) END;
      END;
    END;
  END ConvertToFraction;
 
  PROCEDURE ConvertToExponent(ch: CHAR);
    (* convert a character to the exponent of a constant real number *)
  BEGIN
    IF ch = '-' THEN negexp := TRUE;
    ELSE
      IF eval < 1000 THEN
        eval := eval * 10 + VAL(INTEGER,ORD(ch) - ORD('0'));
      ELSE
        eok := FALSE;
      END;
    END;
  END ConvertToExponent;
 
  PROCEDURE TermRealConst(VAR cval: Constval; VAR err: BOOLEAN);
    (* terminate the calculation of a constant real number *)
    VAR totexp : INTEGER;

    PROCEDURE TenTo(exp: INTEGER): REAL;
      VAR r, res : REAL;
    BEGIN
      res := r1;
      r := r10;
      LOOP
        IF ODD(exp) THEN res := res * r END;
        exp := exp DIV 2;
        IF exp = 0 THEN EXIT END;
        r := r * r;
      END;
      RETURN res
    END TenTo;
 
  BEGIN
    err := FALSE;
    IF eok THEN
      IF negexp THEN DEC(exp,eval) ELSE INC(exp,eval) END;
      totexp := dignum + exp;
      IF totexp > maxexp THEN exp := 0; err := TRUE;
      ELSIF totexp = maxexp THEN
        (* compare with maxfract *);
        WHILE dignum < maxdignum DO
          rval := rval * r10;
          INC(dignum);
          DEC(exp);
        END;
        IF rval >= maxfract THEN exp := 0; err := TRUE END;
      ELSIF totexp < minexp THEN exp := 0; rval := r0;
      END;
      IF exp > 0 THEN (* maximal value is maxexp - 1 *)
        rval := rval * TenTo(exp);
      ELSIF exp < 0 THEN (* minimal value is minexp - maxdignum *)
        IF exp < minexp THEN
          rval := rval / TenTo(minexp - exp);
          exp := minexp;
        END;
        rval := rval / TenTo(- exp);
      END;
    ELSE (* not eok *)
      IF dignum <> 0 THEN err := TRUE END;
    END;
    IF err THEN rval := r0 END;
    NEW(cval.rvalue);
    cval.rvalue^ := rval;
  END TermRealConst;

  PROCEDURE InitFraction(str: String10; VAR fract: REAL);
    VAR ix : CARDINAL;
  BEGIN
    InitRealConst;
    ix := 0;
    WHILE (ix <= 9) AND (str[ix] <> 0C) DO
      ConvertToFraction(str[ix]);
      INC(ix);
    END;
    fract := rval;
  END InitFraction;

BEGIN (* MCP1Reals *)
  r0 := Float(0);
  r1 := Float(1);
  r10 := Float(10);
  InitFraction(maxfractdigits,maxfract);
END MCP1Reals.
