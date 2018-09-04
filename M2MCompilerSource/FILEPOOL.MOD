IMPLEMENTATION MODULE FilePool;     (* LG 06.11.80 *)

  FROM FileSystem IMPORT File;
  FROM Storage IMPORT ALLOCATE, DEALLOCATE;
 
  CONST poolmax = 16;
 
  VAR
    pool : ARRAY [1 .. poolmax] OF FilePointer;
    ix : CARDINAL;
 
  PROCEDURE GetFileNumber(VAR filenum: CARDINAL; VAR error: BOOLEAN);
    VAR ix : CARDINAL;
  BEGIN
    ix := 1;
    WHILE (ix <= poolmax) AND (pool[ix] <> NIL) DO INC(ix) END;
    IF ix <= poolmax THEN
      NEW(pool[ix]);
      filenum := ix;
      error := FALSE;
    ELSE
      filenum := 0;
      error := TRUE;
    END;
  END GetFileNumber;

  PROCEDURE ReturnFileNumber(filenum: CARDINAL);
  BEGIN
    IF (filenum>=1) AND (filenum<=poolmax) THEN
      DISPOSE(pool[filenum]);
    END;
  END ReturnFileNumber;

  PROCEDURE GetFileFromPool(filenum: CARDINAL; VAR file: FilePointer;
                           VAR error: BOOLEAN);
  BEGIN
    IF (filenum >= 1) AND (filenum <= poolmax) THEN
      file := pool[filenum];
      error := file = NIL;
    ELSE
      file := NIL;
      error := TRUE;
    END;
  END GetFileFromPool;

  PROCEDURE ReturnFileToPool(file: FilePointer);
    VAR ix : CARDINAL; 
  BEGIN 
    IF file <> NIL THEN 
      ix := 1; 
      WHILE (ix <= poolmax) AND (pool[ix] <> file) DO INC(ix) END;   
      ReturnFileNumber(ix);
    END;
  END ReturnFileToPool; 
 
BEGIN (* FilePool *)
  ix := 1;
  WHILE ix <= poolmax DO pool[ix] := NIL; INC(ix) END;
END FilePool.
