MODULE Decode; (* Lilith code *)          (* Ch. Jacobi 1.4.81 *)
(*$T-*)
(*$R-*)

(*******************************
 *                             *  
 *    Lilith Decoder           *  
 *    **************           *  
 *                             *  
 *    Version 2.4.81           *  
 *                             *   
 *    Christian Jacobi         *  
 *                             *
 *******************************)


  IMPORT FileSystem, OutFile;
  FROM SYSTEM IMPORT ADDRESS, WORD;
  FROM FileSystem IMPORT 
    File, Lookup, Create, Close, ReadWord, Response, Rename;
  FROM Terminal IMPORT
    Read, ReadAgain, Write, WriteString, WriteLn;
  FROM FileNames IMPORT
    ReadFileName, Identifiers, IdentifierPosition;
  FROM DecoMachineDef IMPORT
    MnemoTab, OpTab, OperandType;


  PROCEDURE ReplaceExtension(newExt: ARRAY OF CHAR; VAR fn: ARRAY OF CHAR);
    VAR i, extPos: CARDINAL;
  BEGIN 
    i := Identifiers(fn);
    IF i=0 THEN extPos := 0
    ELSE
      extPos := IdentifierPosition(fn, i-1)
    END;
    i := 0;
    LOOP
      IF extPos>HIGH(fn) THEN EXIT END;
      IF i>HIGH(newExt) THEN 
        fn[extPos] := 0c; EXIT
      END;
      fn[extPos] := newExt[i];
      INC(i); INC(extPos)
    END 
  END ReplaceExtension;


  
  CONST
    modules   = 64; (* maximal number of modules *)
    maxframelength = 2500; (* maximal length of a codeframe  *)
    maxmodid  = 15;
    alt       = 33C;
    cr        = 15C;
    bell      =  7C;
    date = " 2.4.81";

  TYPE
    Symbol = (eofsy, codekeysy, modulesy, importsy,
              ctext, dtext, fixup);
    ModIdent = ARRAY [0..maxmodid] OF CHAR;
    ModNam = RECORD
               id: ModIdent;
               key: ARRAY [0..2] OF CARDINAL;
             END;

    Modindex = [0..modules-1];
    Modcard  = [0..modules];
 

  VAR
    mn: ModNam;
    codekey: CARDINAL;
    fn: ARRAY [0..40] OF CHAR;
    default: BOOLEAN;
    reply: INTEGER;
    i: CARDINAL;
    ch: CHAR;
    inf: File;     
    outf: File;     

  
  MODULE ErrorModule;
 
    IMPORT WriteString, WriteLn; 
    EXPORT errors, ErrorType, Error; 
 
    TYPE 
      ErrorType = (eofer, frer, syer, cker, mner, sqer, cfer, fler, 
                   fuer, mser);
 
    VAR
      errors: CARDINAL;
 
    PROCEDURE Error(er: ErrorType);
    BEGIN 
      INC(errors); 
      IF errors <= 20 THEN
        CASE er OF
          eofer: WriteString(' try to read past eof') |
          frer:  WriteString(' frameerror') |
          syer:  WriteString(' illegal symbol read') |
          cker:  WriteString(' incorrect type of code') |
          mner:  WriteString(' illegal modulename read') |
          sqer:  WriteString(' symbol sequence error') |
          cfer:  WriteString(' file not a .RLP file') |
          fler:  WriteString(' incorrect framelength') |
          fuer:  WriteString(' fixup error') |
          mser:  WriteString(' top of loadable area reached') 
        END;
        WriteLn;
      END;
    END Error;
 
  BEGIN
    errors := 0;
  END ErrorModule;
 

 MODULE InCode;

    IMPORT inf; 
    FROM FileSystem IMPORT  
      File, ReadWord, Response; 
    IMPORT Symbol, Error, ErrorType, ModNam;

    EXPORT
      Getnum, Getsy, sy, fs, Skip, InitInCode, TermInCode;

    VAR 
      sy: Symbol; fs: CARDINAL;
      nextn: CARDINAL;

    PROCEDURE Getnum(VAR n: CARDINAL);
    BEGIN
      IF fs = 0 THEN Error(frer); n := 0
      ELSE DEC(fs);
        IF inf.eof THEN
          n := 0; 
          IF fs = 0 THEN Error(frer) END;
        ELSE
          n := nextn; 
          ReadWord(inf, nextn);
        END
      END
    END Getnum;

    PROCEDURE Skip;
      VAR n: CARDINAL;
    BEGIN
      WHILE fs>0 DO Getnum(n) END;
    END Skip;

    PROCEDURE Getsy;
      VAR n: CARDINAL; 
    BEGIN
      IF fs > 0 THEN Error(frer); Skip END; 
      IF inf.eof THEN sy := eofsy 
      ELSE
        fs := 1; Getnum(n);
        IF (200B <= n) AND (n <= 205B) THEN 
          sy := Symbol(n - 177B);
          fs := 1; Getnum(fs);
        ELSE sy := eofsy; Error(syer)
        END;
      END;
    END Getsy;

    PROCEDURE InitInCode;
    BEGIN
      ReadWord(inf, nextn); fs := 0;
    END InitInCode;
    
    PROCEDURE TermInCode;
    BEGIN
    END TermInCode;
    
  END InCode;
   
    
  MODULE OutputForDecoder;
    IMPORT OutFile, outf, MnemoTab, WORD;
           (* MnemoTab should be local, it is imported for the reason that
              the initialisation of Mnemotab is done together with the
              initialisation of the operand's table OpTab *)

    EXPORT WriteOctByte, WriteOctWord, WriteMnemonic, Space, Spaces,
           Line, WriteWriteString, TermOutFile, InitOutFile, WriteCh; 
    

    PROCEDURE WriteCh(ch: CHAR);
    BEGIN OutFile.WriteChar(outf,ch)
    END WriteCh;

    PROCEDURE Space;
    BEGIN OutFile.WriteChar(outf,' ')
    END Space;

    PROCEDURE Spaces(i: CARDINAL);
      VAR l: CARDINAL;
    BEGIN
      FOR l := 1 TO i DO OutFile.WriteChar(outf,' ') END
    END Spaces;

    PROCEDURE Line;
    BEGIN
      OutFile.WriteLine(outf);
    END Line;

    PROCEDURE WriteWriteString(s: ARRAY OF CHAR);
    BEGIN
      OutFile.WriteWriteString(outf,s,1);
    END WriteWriteString;

    PROCEDURE WriteOctByte(w: WORD);
    BEGIN
      OutFile.WriteOct(outf,w,3)
    END WriteOctByte;
  
    PROCEDURE WriteOctWord(w: WORD);
    BEGIN
      OutFile.WriteOct(outf,w,5)
    END WriteOctWord;

    PROCEDURE WriteMnemonic(i: CARDINAL);
    BEGIN 
      OutFile.WriteWriteString(outf,MnemoTab[i],1) 
    END WriteMnemonic;
  
    PROCEDURE TermOutFile;
    BEGIN
      OutFile.WriteWriteString(outf,'end decode',1); OutFile.WriteLine(outf);
    END TermOutFile;

    PROCEDURE InitOutFile;
    BEGIN
    END InitOutFile;

  END OutputForDecoder;



    
  PROCEDURE OutModIdent(id: ModIdent);
    VAR i: CARDINAL;
  BEGIN
    Space;
    FOR i := 0 TO maxmodid DO WriteCh(id[i]) END;
  END OutModIdent;


  PROCEDURE LoadFile;

    VAR codebase: CARDINAL;
        database: CARDINAL;
 
    PROCEDURE Getmn(VAR mn: ModNam);

      VAR c, n: CARDINAL; 
          ch: CHAR; 
          oddpos: BOOLEAN; 
          idend : BOOLEAN;

      PROCEDURE Getch(VAR ch: CHAR);
      BEGIN
        IF oddpos THEN ch := CHAR( n MOD 400B)
        ELSE Getnum(n); ch := CHAR( n DIV 400B)
        END;
        oddpos := NOT oddpos;
        IF (ch < 40C) OR (177C < ch) THEN ch := ' ' END;
      END Getch;

    BEGIN
      oddpos := FALSE;
      IF fs >= 11 THEN
        WITH mn DO 
          idend := FALSE;
          FOR c := 0 TO 15 DO
            Getch(ch);
            IF idend THEN ch := ' ' END;
            idend := ch = ' ';
            id[c] := ch;
          END;  
          FOR c := 0 TO 2 DO Getnum(key[c]) END;      
        END; 
      ELSE Error(mner); Skip
      END
    END Getmn;

     
    PROCEDURE CodeKey;
      VAR actcodekey: CARDINAL;
    BEGIN
      Line; WriteWriteString("codekey    = "); 
      IF sy = codekeysy THEN
        IF fs = 1 THEN
          Getnum(actcodekey); Getsy;
          WriteOctWord(actcodekey);
        ELSE Error(fler); Skip; sy := eofsy;
        END
      END;
      Line;
    END CodeKey;


    PROCEDURE ModuleHeader; 
      VAR mn: ModNam; mnr: Modcard; 
          datasize: CARDINAL; 
          i, j: CARDINAL;
    BEGIN 
      WriteWriteString("module name: ");
      IF fs <> 12 THEN Error(fler); Skip; sy := eofsy;
      ELSE Getmn(mn); OutModIdent(mn.id); Line;
        Getnum(datasize); Getsy;  
        WriteWriteString("datasize   = "); WriteOctWord(datasize); Line;
        WriteWriteString("key          ");
          WITH mn DO
            FOR i := 0 TO 2 DO
              WriteOctWord(key[i]); Space;
            END;
          END;
        Line; 
      END     
    END ModuleHeader; 

 
    PROCEDURE Imports; 
      VAR mn: ModNam; mnr: Modcard;
    BEGIN     
      WriteWriteString("import "); 
      mnr := 0;
      WHILE fs >= 11 DO 
        Getmn(mn); INC(mnr);
        IF mnr<>1 THEN Spaces(7) END; OutModIdent(mn.id);
        WriteWriteString(" is # "); WriteOctByte(mnr); Line;
      END; 
      IF fs <> 0 THEN Error(fler); Skip END; 
      Getsy; Line; 
    END Imports; 

 
    PROCEDURE LoadCode; 
      VAR offset: CARDINAL; 
          floc,i : CARDINAL; 
          nr: Modcard; 

  MODULE InputForDecoder;
      IMPORT Getnum, fs;
      EXPORT LoadAddress, ByteAddress, Byte,
             GetNext, StartAt, endReached;

    VAR ByteAddress: CARDINAL;
        LoadAddress: CARDINAL;
        Byte:        CARDINAL; (* currend input byte *)
        endReached:  BOOLEAN;  (* if endReached then Byte is not defined *)

    VAR NewWord:     BOOLEAN;  (* next byte is onto a new word *)
        lword:       CARDINAL;
  
    PROCEDURE GetNext;
    BEGIN INC(ByteAddress);
      IF NewWord THEN 
        IF fs>0 THEN Getnum(lword) ELSE endReached := TRUE; lword := 0 END;
        Byte := lword DIV 100H;
        INC(LoadAddress);
        NewWord := FALSE;
      ELSE
        Byte := lword MOD 100H;
        NewWord := TRUE;
     END;
    END GetNext;

    PROCEDURE StartAt(loadadr: CARDINAL);
    BEGIN
      endReached := FALSE;
      NewWord := TRUE; 
      ByteAddress := loadadr*2-1;
      LoadAddress := loadadr-1; 
      GetNext;
    END StartAt;

  END InputForDecoder;
  
  PROCEDURE NextWord(): CARDINAL;
    VAR l: CARDINAL;
  BEGIN
    GetNext; l := Byte; GetNext;
    RETURN l*100H+Byte
  END NextWord;

  PROCEDURE Instruction;
    VAR k,l: CARDINAL;
  BEGIN
    WriteOctByte(Byte); 
    Spaces(7);
    WriteMnemonic(Byte);
    Space;
    CASE OpTab[Byte] OF

      illegal:

    | none:

    | casejpx:
         k := ByteAddress+1;
         WriteCh("[");
         l := NextWord(); WriteOctWord(l);
         WriteWriteString("] -> ");
         l := k+l; WriteOctWord(l); CaseAt(l); 

    | byte:
         GetNext; WriteOctByte(Byte); Space;

    | twobytes:
         GetNext; WriteOctByte(Byte); Space;
         GetNext; WriteOctByte(Byte); Space;

    | bytejumpf:
         k := ByteAddress+1;
         GetNext;
         WriteCh("["); WriteOctByte(Byte); WriteWriteString("]   -> ");
         l := k+Byte; WriteOctWord(l)

    | bytejumpb:
         k := ByteAddress+1;
         GetNext;
         WriteCh("["); WriteOctByte(Byte); WriteWriteString("]   -> ");
         l := k-Byte; WriteOctWord(l)

    | word:
         l := NextWord();
         WriteOctWord(l); Space;

    | wordjump:
         k := ByteAddress+1;
         l := NextWord();
         WriteCh("["); WriteOctWord(l); WriteWriteString("] -> ");
         l := k+l; WriteOctWord(l)

    | specialrds:
         GetNext; WriteOctByte(Byte); l := Byte; Space;
         FOR k := 0 TO l-1 DO
           GetNext;
           IF k<10 THEN WriteOctByte(Byte); Space END 
         END; 

    | twowords:
         FOR k := 0 TO 1 DO
           GetNext; l := Byte; GetNext;
           WriteOctWord(l*100B+Byte); Space;
         END 

    | for2jump:
         GetNext; WriteOctByte(Byte); Space;
         k := ByteAddress+1;
         l := NextWord();
         WriteCh("["); WriteOctWord(l); WriteWriteString("] -> ");
         l := k+l; WriteOctWord(l)

    | escape:
         WriteWriteString("unknown number of bytes");

    ELSE  WriteString("decoder error"); 
    END
  END Instruction;


  MODULE CaseSystem;
    IMPORT NextWord, WriteOctWord, LoadAddress, ByteAddress,
           Space, Spaces, Line, WriteWriteString, Byte, GetNext;
    EXPORT NextCase, CaseAt, CaseTable;

    VAR NextCase: CARDINAL;
        CaseStack: ARRAY [0..20] OF CARDINAL;
        CaseTop: CARDINAL;

    PROCEDURE CaseAt(loc: CARDINAL);
    BEGIN
      INC(CaseTop); CaseStack[CaseTop] := loc; NextCase := loc;
    END CaseAt;

    PROCEDURE CaseTable;
      VAR Lower, Upper, i: INTEGER; l: CARDINAL;
    BEGIN DEC(CaseTop); NextCase := CaseStack[CaseTop];

      Lower := Byte; GetNext; Lower := INTEGER(CARDINAL(Lower)*100H+Byte);
      WriteOctWord(LoadAddress); Space;
      WriteOctWord(ByteAddress-1); Space; WriteOctWord(Lower); 
      Spaces(10); WriteOctWord(Lower); WriteWriteString("    Low"); Line;

      Upper := INTEGER(NextWord());
      WriteOctWord(LoadAddress); Space;
      WriteOctWord(ByteAddress-1); Space; WriteOctWord(Upper);
      Spaces(10); WriteOctWord(Upper); WriteWriteString("    High"); Line;

      l := NextWord();  (* Else *)
      WriteOctWord(LoadAddress); Space;
      WriteOctWord(ByteAddress-1); Space; WriteOctWord(l); Spaces(10);
      WriteWriteString("-> "); WriteOctWord(ByteAddress-1+CARDINAL(l)); 
      WriteWriteString(" Else");

      FOR i := 0 TO Upper-Lower DO
        Line; l := NextWord();  (* Offset *)
        WriteOctWord(LoadAddress); Space;
        WriteOctWord(ByteAddress-1); Space; WriteOctWord(l); Spaces(10);
        WriteWriteString("-> "); WriteOctWord(ByteAddress-1+CARDINAL(l)); 
      END;

      WriteWriteString(" End");
    END CaseTable;

  BEGIN
    CaseStack[0] := 0; NextCase := 0;
    CaseTop := 0;
  END CaseSystem;

  PROCEDURE Decode;
  BEGIN
    StartAt(offset);
    WHILE NOT endReached DO
      IF ByteAddress=NextCase THEN CaseTable
      ELSE
        WriteOctWord(LoadAddress); Space;
        WriteOctWord(ByteAddress); Space;
        Instruction
      END;
      Line; 
      GetNext;
    END
  END Decode;


    BEGIN  
      IF fs = 0 THEN Error(fler)
      ELSE Getnum(offset);
        IF probablyprocnum AND (fs=1) THEN 
          WriteWriteString("procedure  # "); WriteOctByte(offset);
          WriteWriteString(" at "); Getnum(i); WriteOctWord(i); 
          WriteWriteString(" bytes relative to F"); Line;
          Getsy;
        ELSE
          WriteWriteString("code at F + "); WriteOctWord(offset); 
          WriteWriteString(" words "); Line;
          Decode; Getsy;
          IF sy = fixup THEN 
            WriteWriteString("fixups at "); i := 0;
            WHILE fs > 0 DO 
              i := (i+1) MOD 9;
              IF i=0 THEN Line; Spaces(10); INC(i) END;
              Getnum(floc);   
              WriteOctWord(floc); Space;
            END; (* WHILE *) 
            Getsy; Line
          END; (* IF sy = fixup *) 
          Line; 
        END;
      END; (* IF fs = 0 *)
    END LoadCode; 

 
    PROCEDURE LoadData; 
      VAR offset, n: CARDINAL; 
    BEGIN
      WriteWriteString("data, relative to G"); Line;
      IF fs = 0 THEN Error(fler) 
      ELSE Getnum(offset);   
          WHILE fs > 0 DO 
            Getnum(n); 
            WriteOctWord(offset); WriteWriteString(":  ");
            WriteOctWord(n); Line;
            INC(offset)
          END
      END;
      Getsy; Line; 
    END LoadData; 

    VAR probablyprocnum: BOOLEAN;

  BEGIN (* LoadFile *) 
    InitInCode; 
    Getsy;     
    REPEAT
      IF sy=codekeysy THEN CodeKey END;;
      IF sy = modulesy THEN
        ModuleHeader; 
        IF sy = importsy THEN Imports END;
        probablyprocnum := TRUE;
        WHILE (sy = ctext) OR (sy = dtext) DO 
          IF sy = ctext THEN
            LoadCode; probablyprocnum := NOT probablyprocnum 
          ELSE 
            LoadData 
          END 
        END; (* WHILE *) 
        IF NOT ((sy=eofsy) OR (sy=modulesy) OR (sy=codekeysy)) THEN
          Error(sqer); 
          REPEAT 
            Skip; 
            Getsy; 
          UNTIL (sy=eofsy) OR (sy=modulesy) OR (sy=codekeysy); 
        END;
      ELSE Error(cfer)
      END;
    UNTIL sy=eofsy;
    TermInCode;
  END LoadFile;
   
  VAR ok: BOOLEAN;

BEGIN
  WriteString('decode '); 
  LOOP ok := FALSE;
    WriteString(' >');
    ReadFileName(fn, 'DK..OBJ');
    Read(ch);
    IF ch=33C THEN 
      WriteString(' no file'); RETURN
    END;
    default := TRUE;      
      Lookup(inf, fn, FALSE);
      IF inf.res=done THEN ok := TRUE; EXIT
      ELSE                
        WriteString(' not done'); WriteLn;
      END;
  END;
  WriteLn;
  ReplaceExtension("DEC", fn);
  Lookup(outf, fn, TRUE);  (* create new file *) 
    InitOutFile;
    WriteWriteString("decode  version"); 
    WriteWriteString(date); Line;
  
      IF ok (* inf found *) THEN
        LoadFile; Close(inf);     
      ELSE INC(errors);
      END;
  
    TermOutFile; 
    Close(outf);
    IF errors > 0 THEN
      WriteString(' decode unsuccessfull'); WriteLn;  
    END;
END Decode.
