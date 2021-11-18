IMPLEMENTATION MODULE M3DL; (*NW 2.1.84 / 27.5.85*)
  FROM Heap IMPORT Allocate;
  FROM Terminal IMPORT WriteString;
  FROM SYSTEM IMPORT ADDRESS;

  CONST StackSize = 10000;

  VAR current, last: ADDRESS;

  PROCEDURE Size(): CARDINAL;
    CODE 247B; 4; 24B; 0; 271B  (*H-L*)
  END Size;

  PROCEDURE ALLOCATE(VAR a: ADDRESS; n: CARDINAL);
  BEGIN
    IF (last <= 177777B - n) & (last + n < current) THEN
      current := current - n; a := current
    ELSE WriteString(" not enough heap space"); HALT
    END
  END ALLOCATE;

  PROCEDURE Available(): CARDINAL;
  BEGIN RETURN current - last
  END Available;

  PROCEDURE ResetHeap(a: ADDRESS);
  BEGIN current := a
  END ResetHeap;

BEGIN Allocate(current, 4); Allocate(last, Size() - StackSize)
END M3DL.
