(****************************************
*                                       *
*     MODULA-2 Multi-Pass Compiler      *
*     ****************************      *
*                                       *
*     Implementation for Lilith         *
*                                       *
*                                       *
*     MCOperations:                     *
*                                       * 
*     Arithmetic operations for         *
*     constant expression evaluation    *
*                                       * 
*     Version C18 of 11.09.81           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

IMPLEMENTATION MODULE MCOperations;        (* LG *)
    (* $T-,R- *)

    (* operations on constant expressions in compiler *)
    (* CAUTION: operations are based on 16-bit arithmetic *)
 
    FROM SYSTEM IMPORT TSIZE;
    FROM MCBase IMPORT
      Stptr, Symbol, Structform, Constval,
      intptr, cardptr, intcarptr, realptr, boolptr;
 
(* in definition  module:
    EXPORT QUALIFIED RelOp, AddOp, MulOp, NotOp;
*)
 
    CONST maxint =   77777B; (* maximal integer value *)
          maxcard = 177777B; (* maximal cardinal value *)
 
    PROCEDURE RelOp(c1,c2: Constval; VAR res: Constval; op: Symbol;
                    tp: Stptr; VAR err: BOOLEAN);
      (* evaluation of a relational operation on constant values *)

      (* reals not implemented *)
 
      VAR bool : BOOLEAN;
          v1, v2 : CARDINAL;
    BEGIN
      err := tp = realptr;
      v1 := c1.value; v2 := c2.value;
      CASE op OF
        eql: bool := v1 = v2;
       |neq: bool := v1 <> v2;
       |leq: 
          IF tp^.form = sets THEN bool := BITSET(v1) <= BITSET(v2);
          ELSIF tp = intptr THEN bool := INTEGER(v1) <= INTEGER(v2);
          ELSE bool := v1 <= v2;
          END;
       |geq:
          IF tp^.form = sets THEN bool := BITSET(v1) >= BITSET(v2);
          ELSIF tp = intptr THEN bool := INTEGER(v1) >= INTEGER(v2);
          ELSE bool := v1 >= v2;
          END;
       |lss:
          IF tp = intptr THEN bool := INTEGER(v1) < INTEGER(v2);
          ELSE bool := v1 < v2
          END;
       |grt:
          IF tp = intptr THEN bool := INTEGER(v1) > INTEGER(v2);
          ELSE bool := v1 > v2;
          END;
       |insy:
          IF TSIZE(CARDINAL) = 1 THEN (* on Lilith *)
            bool := v1 IN BITSET(v2);
          ELSE (* on PDP-11 *)
            (* inverse bit order on Lilith *)
            bool := 15 - v1 IN BITSET(v2);
          END;
      END;
      IF err THEN bool := FALSE END;
      res.value := CARDINAL(bool);
    END RelOp;

    PROCEDURE AddOp(c1,c2: Constval; VAR res: Constval; op: Symbol;
                    VAR tp: Stptr; VAR err: BOOLEAN); 
      (* evaluation of additional operations on constant values *)
      (* return the result value by res and the result type by tp *)
      (* err indicates an overflow error *) 
 
      (* reals not implemented *) 

      VAR v1, v2, v3 : CARDINAL;
          save : CARDINAL; (* for INTEGER subtraction *)
    BEGIN
      v1 := c1.value; v2 := c2.value;
      err := FALSE; 
      IF (tp = intcarptr) OR (tp = cardptr) THEN
        (* simulation of cardinal arithmetik *)
        IF op = plus THEN
          IF maxcard - v2 >= v1 THEN
            v3 := v1 + v2;
            IF (tp = intcarptr) AND (v3 > maxint) THEN tp := cardptr END;
          ELSE err := TRUE;
          END;
        ELSE (* op = minus *)
          IF v2 <= v1 THEN
            v3 := v1 - v2;
          ELSIF tp = intcarptr THEN
            v3 := CARDINAL(INTEGER(v1) - INTEGER(v2));
            tp := intptr;
          ELSE err := TRUE;
          END; 
        END; 
      ELSIF tp = intptr THEN (* simulation of integer arithmetic *)
        save := 0;
        IF op = minus THEN (* invert operation *)
          IF v2 = maxint + 1 THEN (* maximal negative number *)
            v2 := maxint;
            save := 1;
          ELSIF v2 <> 0 THEN v2 := maxcard - v2 + 1;
          END;
        END;
        IF (v1 <= maxint) AND (v2 <= maxint) THEN
          v3 := v1 + v2 + save;
          err := v3 > maxint;
        ELSIF (v1 > maxint) AND (v2 > maxint) THEN
          v2 := maxcard - v2 + 1;
          v3 := v1 - v2; (* save is always zero *)
          err := v3 <= maxint;
        ELSE
          v3 := CARDINAL(INTEGER(v1) + INTEGER(v2) + INTEGER(save));
        END;
      ELSIF tp = realptr THEN
        IF (op=minus) AND (c1.rvalue=NIL) AND (c2.rvalue<>NIL) THEN
          (* sign inversion *)
          c2.rvalue^ := - c2.rvalue^;
          v3 := v2; (* pointer value *)
        ELSE
          err := TRUE; (* not implemented *) 
        END;
      ELSIF tp = boolptr THEN   
        IF op = orsy THEN 
          v3 := CARDINAL(BOOLEAN(v1) OR BOOLEAN(v2));
        END; 
      ELSIF tp^.form = sets THEN
        IF op = plus THEN v3 := CARDINAL(BITSET(v1) + BITSET(v2));
        ELSE v3 := CARDINAL(BITSET(v1) - BITSET(v2));
        END;
      END; 
      IF err THEN v3 := 0 END;
      res.value := v3;
    END AddOp; 

    PROCEDURE MulOp(c1,c2: Constval; VAR res: Constval; op: Symbol; 
                    VAR tp: Stptr; VAR err: BOOLEAN); 
      (* evaluation of multiplicational operations on constant values *)
      (* return the result value by res and the result type by tp *)
      (* err indicates an overflow or zero-division error *) 
 
      (* reals not implemented *)

      VAR v1, v2, v3 : CARDINAL;
          pos : BOOLEAN;

      PROCEDURE Mul;
        (* multiplication of positive values v1 and v2; result to v3 *)
        (* use CARDINAL arithmetic only *)
        VAR prod, d, h: CARDINAL;
            flag : BOOLEAN; (* is set if d becomes too big *)
      BEGIN
        flag := FALSE;
        prod := 0;
        IF v1 < v2 THEN h := v1; d := v2 ELSE h := v2; d := v1 END;
        LOOP
          IF h = 0 THEN EXIT END;
          IF ODD(h) THEN 
            IF flag OR (prod > maxcard - d) THEN (* overflow occured *)
              prod := 0;
              err := TRUE;
              EXIT;
            ELSE prod := prod + d;
            END;
          END;
          h := h DIV 2;
          IF d > maxint THEN flag := TRUE ELSE d := 2 * d END;
        END; (* LOOP *)
        v3 := prod;
      END Mul;
                                  
      PROCEDURE DivMod;
        (* DIV or MOD of values v1 and v2 simulated with *)
        (* CARDINAL arithmetic. Result is assigned to v3 *) 
        VAR r, q, d: CARDINAL;
      BEGIN
        IF v2 = 0 THEN err := TRUE; v3 := 0
        ELSE
          r := v1;
          q := 0;
          d := v2;
          WHILE (d < r) AND (d <= maxint) DO d := d * 2 END;
          LOOP
            IF r >= d THEN r := r - d; q := q + 1; END;
            IF d = v2 THEN EXIT END;
            q := q * 2;
            d := d DIV 2;
          END;
          IF op = divsy THEN v3 := q ELSE v3 := r END;
        END;
      END DivMod;
 
    BEGIN
      v1 := c1.value; v2 := c2.value;
      err := FALSE;  
      IF (tp = intcarptr) OR (tp = cardptr) THEN
        IF op = times THEN
          Mul;
          IF NOT err THEN 
            IF (tp = intcarptr) AND (v3 > maxint) THEN tp := cardptr END;
          END;
        ELSIF (op = divsy) OR (op = modsy) THEN   
          DivMod; 
        END; 
      ELSIF tp = intptr THEN
        pos := TRUE;
        IF v1 > maxint THEN pos := NOT pos; v1 := maxcard - v1 + 1 END;
        IF v2 > maxint THEN pos := NOT pos; v2 := maxcard - v2 + 1 END;
        IF op = times THEN
          Mul;
          IF NOT err THEN
            IF pos THEN err := v3 > maxint;
            ELSE err := v3 > maxint + 1; v3 := maxcard - v3 + 1;
            END;
          END;
        ELSIF (op = divsy) OR (op = modsy) THEN
          DivMod; 
          IF NOT err THEN 
            IF pos THEN err := v3 > maxint;
            ELSE v3 := maxcard - v3 + 1;
            END;
          END;
        END;
      ELSIF tp = realptr THEN err := TRUE; (* not implemented *) 
      ELSIF tp = boolptr THEN 
        IF op = andsy THEN  
          v3 := CARDINAL(BOOLEAN(v1) AND BOOLEAN(v2)); 
        END; 
      ELSIF tp^.form = sets THEN
        IF op = times THEN
          v3 := CARDINAL(BITSET(v1) * BITSET(v2));
        ELSIF op = slash THEN
          v3 := CARDINAL(BITSET(v1) / BITSET(v2));
        END;
      END;
      IF err THEN v3 := 0 END;
      res.value := v3;
    END MulOp;

    PROCEDURE NotOp(c1: Constval; VAR res: Constval);
      (* evaluation of NOT operation on a constant value *)
    BEGIN
      res.value := CARDINAL(NOT BOOLEAN(c1.value));
    END NotOp;

  END MCOperations.

