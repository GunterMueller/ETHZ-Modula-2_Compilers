IMPLEMENTATION MODULE NewStreams;     (* LG 14.10.80 *)
  (* implementation for Personal Computer *)
  (* uses special SYS M-codes directly  - RS 10.8.83 *)
 
  IMPORT FileSystem, FilePool;
  FROM SYSTEM IMPORT WORD, TSIZE;
  FROM FileSystem IMPORT Response;
  FROM Terminal IMPORT WriteString, WriteLn;

  CONST eofc = 0C;

  TYPE STREAM = FilePool.FilePointer;

  (* system M-codes for portable interpreter *)

  PROCEDURE setopen(VAR f: File); 
  CODE 247b; 109 END SetOpen;

  PROCEDURE setpos(VAR f: File; high, low: CARDINAL);
  CODE 247b; 111  END SetPos;   

  PROCEDURE close(VAR f: File); 
  CODE 247b; 103 END Close; 

  PROCEDURE readword(VAR f: File; VAR w: WORD);
  CODE 247b; 115 END ReadWord;

  PROCEDURE readchar(VAR f: File; VAR ch: CHAR);
  CODE 247b; 116 END ReadChar;

  PROCEDURE writeword(VAR f: File; w: WORD);
  CODE 247b; 117 END WriteWord;

  PROCEDURE writechar(VAR f: File; ch: CHAR);
  CODE 247b; 118 END WriteChar;

  PROCEDURE setpos(VAR f: File; high, low: CARDINAL);
  CODE 247b; 111  END SetPos;   

  PROCEDURE getpos(VAR f: File; VAR high, low: CARDINAL);   
  CODE 247b; 112 END GetPos;


  PROCEDURE Error(VAR s: STREAM);
  BEGIN
    WriteString(" ---- illegal operation on stream");
    WriteLn;
    HALT;
  END Error;

  PROCEDURE Reset(s: STREAM);
  BEGIN 
    setopen(s^);
    setpos(s^, 0, 0)
  END Reset;

  PROCEDURE Connect(VAR s: STREAM; filenum: CARDINAL; ws: BOOLEAN);
    VAR err : BOOLEAN;
  BEGIN
    FilePool.GetFileFromPool(filenum,s,err);
    IF err THEN Error(s);
    ELSE Reset(s);
    END;
  END Connect;
  
  PROCEDURE Disconnect(VAR s: STREAM; closefile: BOOLEAN);
  BEGIN
    IF closefile THEN
      close(s^);
      IF s^.res <> done THEN Error(s) END;
      FilePool.ReturnFileToPool(s);
    END; 
  END Disconnect;

  PROCEDURE WriteWord(s: STREAM; w: WORD);
  BEGIN
    writeword(s^,w);
  END WriteWord;

  PROCEDURE WriteChar(s: STREAM; ch: CHAR);
  BEGIN
   writechar(s^,ch);
  END WriteChar;

  PROCEDURE EndWrite(s: STREAM);
  BEGIN
    setopen(s^);
    IF s^.res <> done THEN Error(s) END;
  END EndWrite;

  PROCEDURE ReadWord(s: STREAM; VAR w: WORD);
  BEGIN
    readword(s^,w);
  END ReadWord;

  PROCEDURE ReadChar(s: STREAM; VAR ch: CHAR);
  BEGIN
    readchar(s^,ch); 
  END ReadChar;

  PROCEDURE EOS(s: STREAM): BOOLEAN;
  BEGIN
    RETURN s^.eof;
  END EOS;

  PROCEDURE GetPos(s: STREAM; VAR highpos, lowpos: CARDINAL);
  BEGIN
    getpos(s^,highpos,lowpos);
  END GetPos;

  PROCEDURE SetPos(s: STREAM; highpos, lowpos: CARDINAL);
  BEGIN
    setpos(s^,highpos,lowpos);
  END SetPos;

BEGIN (* NewStreams *)
  eolc := 36C;
END NewStreams.
