IMPLEMENTATION MODULE WriteStrings;  (* AG/LG 17.02.81 *)
  (* $T-,R- *)

  FROM Terminal IMPORT Write;
(* (* definitions from definition module *)

  EXPORT QUALIFIED WriteString, WriteLn;

  PROCEDURE WriteString(str: ARRAY OF CHAR);

  PROCEDURE WriteLn;

(* end definitions *) *)

  PROCEDURE WriteString(str: ARRAY OF CHAR);
    VAR ix : CARDINAL;
  BEGIN
    ix := 0;
    WHILE (ix <= HIGH(str)) AND (str[ix] <> 0C) DO
      Write(str[ix]);
      INC(ix);
    END;
  END WriteString;

  PROCEDURE WriteLn;
  BEGIN
    Write(36C);
  END WriteLn;

  (* $T= *)
END WriteStrings.
