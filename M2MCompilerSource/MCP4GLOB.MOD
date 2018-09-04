IMPLEMENTATION MODULE MCP4Global;   (* Ch. Jacobi 5.4.81 *)

  (* $T-,R- *)

(* global variables and procedures 
   for Pass 4 of the Compiler for the Lilith Computer *)
(* modified to put 32767 out as an invalid line number to indicate eop *)


  IMPORT 
    SYSTEM, NewStreams, MCPublic, MCBase, MCP4CodeSys;
  FROM (*Terminal*) WriteStrings IMPORT 
    WriteString, WriteLn;
    (* Terminal and WriteStrings have identical 
       procedures WriteString and WriteLn!
       for medos operative system use Terminal
       for compiler transportation use WriteStrings *)

MODULE io;
  FROM SYSTEM IMPORT WORD;
  FROM NewStreams IMPORT
    STREAM, Connect, Disconnect, Reset, EndWrite, 
    WriteWord, ReadWord;
  FROM MCPublic IMPORT 
    objFile, il1File, il2File;
  EXPORT 
    WriteCodeWord, ReadInputWord, WriteIntermediateWord, 
    CloseIO, MarkCodePos, inputStream;

  VAR 
    outputStream: STREAM;   
    inputStream:  STREAM;
    codeStream:   STREAM;


  PROCEDURE WriteCodeWord(w: WORD);
  BEGIN
    WriteWord(codeStream, w)
  END WriteCodeWord;

  PROCEDURE ReadInputWord(VAR w: WORD);
  BEGIN
    ReadWord(inputStream, w)
  END ReadInputWord;

  PROCEDURE WriteIntermediateWord(w: WORD);
  BEGIN
    WriteWord(outputStream, w)
  END WriteIntermediateWord;

  PROCEDURE MarkCodePos;
  BEGIN
  END MarkCodePos;
 
  PROCEDURE CloseIO;
  BEGIN
    (* code file *)
         EndWrite(codeStream);
         Disconnect(codeStream, FALSE);
    (* intermediate file for listing *)
  (**)   WriteWord(outputStream,32767); (* This is a code word that the lister can *)
         EndWrite(outputStream);        (* use to detect eop *)
         Disconnect(outputStream, FALSE);
    (* input file *)
         Disconnect(inputStream, FALSE)  
  END CloseIO;


BEGIN
  (* open files *)
  (* Intermediate file for listing *)
       Connect(outputStream, il2File, TRUE);  
       Reset(outputStream);
  (* code file *)
       Connect(codeStream, objFile, TRUE);  
  (* input file *)
       Connect(inputStream, il1File, TRUE);
       Reset(inputStream) 
END io;



MODULE Scanner;
  FROM MCBase IMPORT 
    Symbol, Idptr, Stptr, Stringptr;
  FROM NewStreams IMPORT 
    ReadWord, EOS;
  FROM io IMPORT 
    ReadInputWord, WriteIntermediateWord, inputStream;
  FROM Globals IMPORT 
    CompilerError;
  FROM MCP4CodeSys IMPORT 
    PC;
  IMPORT
    loadAddress,
    sy, val, nptr, cstPtr, cString, 
    controlRangeCheck, arithmeticRangeCheck;
  EXPORT 
    GetSymbol, position, line;


  VAR
    position: CARDINAL; (* Position within a line; set for each Symbol *)
    line: CARDINAL;     (* line number; set for each Symbol *) 

 
    PROCEDURE PutLineHeader;
    BEGIN 
      WriteIntermediateWord(line);
      WriteIntermediateWord(CARDINAL(PC)+2*loadAddress);
    END PutLineHeader;


    PROCEDURE OptionCode;   
      (* Treat a compiler directive *)
    BEGIN  
      IF CHAR(val) = 'T' THEN GetSymbol;  
        controlRangeCheck := sy = plus   
      ELSIF CHAR(val) = 'R' THEN GetSymbol;  
        arithmeticRangeCheck := sy = plus   
      ELSE
        GetSymbol 
      END;  
      GetSymbol
    END OptionCode;  
  

    PROCEDURE GetSymbol;   
      (* Read one Symbol (skipping the eol)
         and set exported variables *)
    BEGIN
      REPEAT  
        (*ReadInputWord(i);*) ReadWord(inputStream, position);
        IF EOS(inputStream) THEN sy := eop  
        ELSE  
          sy := Symbol(position DIV 400B)
        END;  
        IF sy<proceduresy THEN RETURN END;
        IF (sy=namesy) OR (sy=modulesy) OR (sy=proceduresy) THEN  
          ReadInputWord(nptr)   
        ELSIF sy = eol THEN 
          ReadInputWord(line); PutLineHeader 
        ELSIF sy = field THEN ReadInputWord(val)  
        ELSIF sy = option THEN  
          ReadInputWord(val);  
          OptionCode  
        ELSIF sy=anycon THEN  
          ReadInputWord(cstPtr);  
          ReadInputWord(cString); val := INTEGER(cString)  
        END;  
      UNTIL sy<>eol   
    END GetSymbol;  
  

BEGIN  (* init scanner *)
  controlRangeCheck := TRUE; 
  arithmeticRangeCheck := TRUE; 
  line := 1  
END Scanner;



MODULE Globals;
  FROM MCPublic IMPORT passerrs, compstat;
  FROM MCBase IMPORT procnumber;
  FROM io IMPORT WriteIntermediateWord;
  FROM Scanner IMPORT line, position;
  IMPORT 
    loadCount, level, spPosition, loadAddress,
    WriteString, WriteLn;
  EXPORT 
    Error, CompilerError, Assert;


  PROCEDURE CompilerError;  

    PROCEDURE Debug;
      PROCEDURE WriteCardinal(value: CARDINAL);
        CONST length = 7;
        VAR i: CARDINAL;
            a: ARRAY [0..length-1] OF CHAR;
      BEGIN
        i := length; 
        REPEAT
          DEC(i);
          a[i] := CHAR(value MOD 10 + CARDINAL("0"));
          value := value DIV 10; 
        UNTIL value = 0;
        WHILE i>0 DO DEC(i); a[i] := " " END;
        WriteString(a);
      END WriteCardinal;
    BEGIN (*Debug*)
      WriteString("line "); WriteCardinal(line); 
      WriteString("   position "); WriteCardinal(position); WriteLn;
      WriteString("loadcount "); WriteCardinal(loadCount); 
      WriteString("   loadAddress "); WriteCardinal(loadAddress); WriteLn;
      WriteString("to debug the compiler Chris needs the dump,"); WriteLn;
      WriteString("the text written out above and the source"); WriteLn;
      WriteString("of your program"); WriteLn;
    END Debug;

  BEGIN (*CompilerError*)
    WriteString("Compiler Error "); WriteLn;  
    INCL(compstat, passerrs);  
    Debug;
    HALT (*produces a dump on the medos operative system!*)
  END CompilerError;  
  

  PROCEDURE Assert (fb: BOOLEAN); 
    (*see definition module*)
  BEGIN
    IF NOT fb THEN CompilerError END  
  END Assert;  


  PROCEDURE Error(n: INTEGER);   
  BEGIN  
    WriteIntermediateWord(-n);
    WriteIntermediateWord(position MOD 400B); 
    INCL(compstat, passerrs)  
  END Error;  
    

BEGIN  
  (* init global variables *)
  loadCount := 0;
  level := 0;  
  spPosition := 0;
  loadAddress := procnumber 
                 (*follows the procedure offset table*)
END Globals;


END MCP4Global.
