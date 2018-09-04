(****************************************
*                                       *
*     MODULA-2 Multi-Pass Compiler      *
*     ****************************      *
*                                       *
*     Implementation for Lilith         *
*                                       *
*                                       *
*     MCP2IO:                           *
*                                       * 
*     input / output handling in Pass 2 *
*                                       * 
*     Version C18 of 10.07.81           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

IMPLEMENTATION MODULE MCP2IO;   (* LG *)

  (* $T-,R- *)

  IMPORT SYSTEM, NewStreams, MCBase, MCPublic;

  FROM MCBase IMPORT Keyarr;
  FROM MCPublic IMPORT Compilerstatus, compstat, comptime;

  VAR lpos, lline: CARDINAL;

  MODULE OutputSystem;

    FROM SYSTEM IMPORT WORD;
    FROM NewStreams IMPORT
      STREAM, Connect, Reset, WriteWord, EndWrite, Disconnect;
    FROM MCBase IMPORT Symbol;
    FROM MCPublic IMPORT il2File;
    IMPORT pos;

    EXPORT il2, PutSy, PutWord, StopOutput, RestartOutput, TermOutput;

    VAR il2 : STREAM; 
        output : BOOLEAN; (* output on il2 allowed *)

    PROCEDURE PutSy(s : Symbol);
      (* put Symbol and pos on il2-file *)
    BEGIN 
      IF output THEN WriteWord(il2,ORD(s) * 400B + pos) END
    END PutSy;

    PROCEDURE PutWord(w : WORD);
      (* put word on il2-file *)
    BEGIN 
      IF output THEN WriteWord(il2,w) END
    END PutWord;

    PROCEDURE StopOutput;
    BEGIN
      output := FALSE
    END StopOutput;
  
    PROCEDURE RestartOutput;
    BEGIN
      output := TRUE
    END RestartOutput;

    PROCEDURE TermOutput; 
    BEGIN 
      PutSy(eop); 
      EndWrite(il2);
      Disconnect(il2,FALSE);
    END TermOutput; 

  BEGIN 
    Connect(il2,il2File,TRUE);
    Reset(il2);
    output := TRUE; 
  END OutputSystem; 

  MODULE ErrorSystem; 

    FROM NewStreams IMPORT WriteWord;
    FROM MCBase IMPORT Symbol;
    FROM MCPublic IMPORT Compilerstatus,  compstat;
    IMPORT line, pos, lline, lpos, OutputSystem;

    EXPORT Error, ErrorLS; 

    CONST errmax = 300; 

    VAR errsymval, eolsymval : CARDINAL;
        errcount : CARDINAL;

    PROCEDURE Error(n: CARDINAL);
      (* no suppression of writing on il2 file *)
    BEGIN 
      INC(errcount); INCL(compstat,passerrs);
      IF errcount < errmax THEN 
        WriteWord(il2,errsymval + pos); WriteWord(il2,n); 
      ELSIF errcount = errmax THEN
        WriteWord(il2,errsymval); WriteWord(il2,5); (* too many errors *) 
      END;
    END Error;

    PROCEDURE ErrorLS(n: CARDINAL);
      VAR hpos : CARDINAL; 
    BEGIN 
      hpos := pos; pos := lpos; 
      IF lline <> line THEN 
        WriteWord(il2,eolsymval); WriteWord(il2,lline); 
        Error(n); 
        WriteWord(il2,eolsymval); WriteWord(il2,line);
      ELSE Error(n);
      END;
      pos := hpos;
    END ErrorLS;

  BEGIN 
    errcount := 0;
    EXCL(compstat,passerrs);
    errsymval := ORD(errorsy) * 400B; (* value for errorsy *)
    eolsymval := ORD(eol) * 400B;     (* value for eol *)
  END ErrorSystem;

  MODULE Scanner; 

    FROM NewStreams IMPORT
      STREAM, Connect, Reset, ReadWord, WriteWord, Disconnect;
    FROM MCBase IMPORT Symbol, Spellix;
    FROM MCPublic IMPORT il1File;
    IMPORT
      ErrorSystem, OutputSystem,
      sy, spix, maxspix, val, length,
      pos, line, lpos, lline;

    EXPORT GetSy, PutGetSy, TermInput;

    VAR 
      card : CARDINAL;
      il1 : STREAM; 
      issy : BOOLEAN;

    PROCEDURE GetSy;
    BEGIN (* get next Symbol *)
      lpos := pos; lline := line;
      REPEAT
        issy := TRUE;
        ReadWord(il1,card);
        pos := card MOD 400B;
        sy := VAL(Symbol,card DIV 400B); 
        CASE sy OF
          ident: ReadWord(il1,spix);
         |intcon,cardcon,intcarcon,charcon,realcon: ReadWord(il1,val);
         |stringcon: ReadWord(il1,val); ReadWord(il1,length);
         |option:
            ReadWord(il1,val);
            ReadWord(il1,card);
            PutSy(option);
            PutWord(val); PutWord(card);
            issy := FALSE;
         |errorsy,eol:
            ReadWord(il1,val);
            IF sy = eol THEN line := val END;
            WriteWord(il2,card); WriteWord(il2,val); (* no suppression *)
            issy := FALSE;
          ELSE (* no activity *)
        END; (* case *) 
      UNTIL issy; 
    END GetSy;

    PROCEDURE PutGetSy; 
    BEGIN (* put last Symbol, get next Symbol *)
      PutSy(sy);
      IF sy = ident THEN PutWord(spix)
      ELSIF (sy >= intcon) AND (sy <= stringcon) THEN
        PutWord(val); 
        IF sy = stringcon THEN PutWord(length) END
      END;
      GetSy;
    END PutGetSy; 

    PROCEDURE TermInput;
    BEGIN Disconnect(il1,FALSE); 
    END TermInput;

  BEGIN 
    Connect(il1,il1File,TRUE);
    Reset(il1);
    line := 1; pos := 1;
  END Scanner;

  MODULE AsciiHandling;  (* $T- *)
    (* handling with the identifier-file ASCII *)

    FROM NewStreams IMPORT
      STREAM, Connect, Reset, ReadChar, SetPos, Disconnect; 
    FROM MCBase IMPORT Spellix; 
    FROM MCPublic IMPORT ascFile;
 
    EXPORT AsciiSetPos, AsciiRead, TermAscii; 
 
    VAR asc : STREAM;

    PROCEDURE AsciiSetPos(spix: Spellix); 
      (* set position on ASCII file *) 
    BEGIN 
      SetPos(asc,0,spix);
    END AsciiSetPos; 

    PROCEDURE AsciiRead(VAR ch: CHAR);
      (* read character from ASCII file *)
    BEGIN
      ReadChar(asc,ch);
    END AsciiRead;   

    PROCEDURE TermAscii;
    BEGIN
      Disconnect(asc,FALSE);
    END TermAscii;

  BEGIN (* AsciiHandling *)
    Connect(asc,ascFile,FALSE);
    Reset(asc);
  END AsciiHandling; (* $T= *)

  MODULE SkipInSymbolModule;

    FROM MCBase IMPORT Symbol;
    FROM Scanner IMPORT GetSy;
    IMPORT sy;

    EXPORT SkipConstant, SkipType; 
 
    PROCEDURE Skip(s: Symbol);
    BEGIN
      WHILE sy <> s DO GetSy END;
      GetSy;
    END Skip;

    PROCEDURE SkipQualIdent; 
    BEGIN   
      IF sy = ident THEN   
        GetSy; 
        WHILE sy = period DO GetSy; GetSy END; 
      END; 
    END SkipQualIdent;   
 
    PROCEDURE SkipConstant; 
      (* skip constant in a symbol module *) 
    BEGIN 
      IF sy = cardcon THEN GetSy; SkipQualIdent; 
      ELSIF (sy = stringcon) OR (sy = realcon) THEN GetSy; 
      END; 
    END SkipConstant; 
 
    PROCEDURE SkipType;
      (* skip type structures in a symbol module *)
   
      PROCEDURE SkipVariants;
        (* skip variant structures *)
      BEGIN
        IF sy = casesy THEN 
          Skip(colon); 
          SkipQualIdent; 
          WHILE sy = ofsy DO 
            Skip(colon); 
            SkipVariants; 
            GetSy; (* size *) 
          END; 
          IF sy = elsesy THEN 
            GetSy; 
            SkipVariants; 
            GetSy; (* size *) 
          END; 
          GetSy; (* endsy *) 
        END; 
      END SkipVariants; 

    BEGIN (* SkipType *) 
      CASE sy OF 
        arraysy: Skip(ofsy); SkipType; 
       |recordsy:   
          GetSy; 
          WHILE sy = ident DO Skip(colon); SkipType END; 
          SkipVariants; 
          GetSy; (* endsy *) 
          GetSy; (* size *) 
       |setsy,pointersy: GetSy; SkipType;  
       |proceduresy: 
          Skip(rparent); 
          IF sy = colon THEN GetSy; SkipType END;   
       |hidden: GetSy;   
       |lparent: Skip(rparent);
       |ident: SkipQualIdent;  
       |lbrack: Skip(rbrack);
      END; 
    END SkipType; 

  END SkipInSymbolModule;

  PROCEDURE GetModuleKey(VAR modkey: Keyarr);
    VAR ix : CARDINAL;
  BEGIN
    FOR ix := 0 TO 2 DO modkey[ix] := comptime[ix] END;
  END GetModuleKey;

  PROCEDURE DefModStatus;
  BEGIN
    INCL(compstat,defs);
  END DefModStatus;

  PROCEDURE TermInOut;
  BEGIN
    TermInput; TermOutput; TermAscii;
  END TermInOut;

END MCP2IO.
