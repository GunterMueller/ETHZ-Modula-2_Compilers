MODULE TL;

FROM Terminal IMPORT Read, WriteLn, WriteString, Write;

VAR ch: CHAR;
    lowercase: BOOLEAN;

PROCEDURE TestLink(VAR ch: CHAR):BOOLEAN;
CODE 246B; 0
END TestLink;

BEGIN
  LOOP
    WriteLn;
    WriteString('Character> ');
    Read(ch); Write(ch);
    IF CAP(ch) = 'Q' THEN EXIT END;
    lowercase := TestLink(ch);
    IF lowercase THEN
      WriteLn;
      WriteString('Converted to : ');
      Write(ch)
    END;
  END;
END TL.
