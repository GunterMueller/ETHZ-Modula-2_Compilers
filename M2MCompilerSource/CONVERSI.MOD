(****************************************
*                                       *
*     Conversions:                      *
*                                       * 
*     Number to string conversion       *
*                                       * 
*     Version of 26.02.81               *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

IMPLEMENTATION MODULE Conversions;            (* LG *)

  (* $T- *)
 
  TYPE Basetype = (oct, dec, hex);

  PROCEDURE ConvertNumber(num, len: CARDINAL; btyp: Basetype;
                          neg: BOOLEAN; VAR str: ARRAY OF CHAR);
    (* conversion of a number into a string of characters *)
    (* num must get the absolute value of the number      *)
    (* len is the minimal length of the generated string  *)
    (* neg means: "the number is negative" for btyp = dec *)
 
    VAR digits : ARRAY [1..6] OF CHAR;
        base : CARDINAL;
        cnt, ix, maxlen : CARDINAL;
        dig : CARDINAL;
  BEGIN
    FOR ix := 1 TO 6 DO digits[ix] := '0' END; (* initialisation *)
    IF btyp = oct THEN base := 10B;
    ELSIF btyp = dec THEN base := 10;
    ELSIF btyp = hex THEN base := 10H;
    END;
    cnt := 0;
    REPEAT 
      INC(cnt);
      dig := num MOD base;
      num := num DIV base;
      IF dig < 10 THEN dig := dig + ORD('0');
      ELSE dig := dig - 10 + ORD('A');
      END;
      digits[cnt] := CHR(dig);
    UNTIL num = 0;
    IF btyp = oct THEN cnt := 6;
    ELSIF btyp = hex THEN cnt := 4;
    ELSIF neg THEN
      INC(cnt); digits[cnt] := '-';
    END;
    maxlen := HIGH(str) + 1; (* get maximal length *)
    IF len > maxlen THEN len := maxlen END;
    IF cnt > maxlen THEN cnt := maxlen END;
    ix := 0;
    WHILE len > cnt DO str[ix] := ' '; INC(ix); DEC(len); END;
    WHILE cnt > 0 DO str[ix] := digits[cnt]; INC(ix); DEC(cnt); END;
    IF ix < maxlen THEN str[ix] := 0C END;
  END ConvertNumber;

  PROCEDURE ConvertOctal(num, len: CARDINAL; VAR str: ARRAY OF CHAR);
    (* conversion of an octal number to a string *) 
  BEGIN   
    ConvertNumber(num,len,oct,FALSE,str);  
  END ConvertOctal;   

  PROCEDURE ConvertHex(num, len: CARDINAL; VAR str: ARRAY OF CHAR);
    (* conversion of a hexadecimal number to a string *) 
  BEGIN   
    ConvertNumber(num,len,hex,FALSE,str);  
  END ConvertHex;   

  PROCEDURE ConvertCardinal(num, len: CARDINAL; VAR str: ARRAY OF CHAR);   
    (* conversion of a cardinal decimal number to a string *) 
  BEGIN   
    ConvertNumber(num,len,dec,FALSE,str); 
  END ConvertCardinal;   

  PROCEDURE ConvertInteger(num: INTEGER; len: CARDINAL;   
                           VAR str: ARRAY OF CHAR); 
    (* conversion of an integer decimal number to a string *) 
  BEGIN 
    ConvertNumber(ABS(num),len,dec,num < 0,str); 
  END ConvertInteger; 
     
END Conversions.
