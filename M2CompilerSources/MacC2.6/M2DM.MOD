IMPLEMENTATION MODULE M2DM;  (* NW 20.5.84; WH 19.8.86 *)
  FROM SYSTEM   IMPORT ADDRESS, LONG, VAL;
  FROM System   IMPORT Allocate, Deallocate;
  FROM Terminal IMPORT WriteString;
  CONST MinHeapSize =  30000D;
        MaxHeapSize = 250000D;
        StepSize    =  10000D;
  VAR current, last: ADDRESS; trySize: LONGINT;
  PROCEDURE ALLOCATE(VAR a: ADDRESS; n: CARDINAL);
  BEGIN
    a := current; IF ODD(n) THEN INC(n) END;
    current := current + VAL(ADDRESS,LONG(n));
    IF current >= last THEN WriteString(" not enough heap space"); HALT END
  END ALLOCATE;
  PROCEDURE Available(): CARDINAL;
  BEGIN
    RETURN VAL(CARDINAL, last - current)
  END Available;
  PROCEDURE ResetHeap(a: ADDRESS);
  BEGIN
    current := a
  END ResetHeap;
BEGIN
  trySize := MaxHeapSize;
  LOOP
    Allocate(current, trySize);
    IF current # NIL THEN EXIT END;
    DEC(trySize, StepSize);
    IF trySize < MinHeapSize THEN WriteString(" not enough heap space"); HALT END;
  END;
  Deallocate(current); DEC(trySize, StepSize);
  Allocate(current, trySize);
  last := VAL(LONGINT, current) + trySize;
END M2DM. (* Copyright Departement Informatik, ETH Zuerich, Switzerland, 1992 *)
