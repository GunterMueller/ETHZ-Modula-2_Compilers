(* has modifications in it for use without memoryfiles *)
(* also does not put C18 on front of calls *)
(****************************************
*                                       *
*     MODULA-2 Multi-Pass Compiler      *
*     ****************************      *
*                                       *
*     Implementation for Lilith         *
*                                       *
*     running on Lilith Computer        *
*                                       *
*                                       *
*     MCInit:                           *
*                                       *
*     initialisation part               *
*     of the Modula-2 compiler          *
*                                       *
*     Version C18 of 19.02.82           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

MODULE MCInit;   (* LG *)

  FROM Monitor IMPORT Time;
  FROM FileSystem IMPORT Create, Close, Response;
  FROM FilePool IMPORT
    FilePointer, GetFileNumber, GetFileFromPool, ReturnFileNumber;
  FROM FileLookup IMPORT LookupFile;
  FROM Options IMPORT GetOption;
  FROM FileNames IMPORT Identifiers, IdentifierPosition;
  FROM WriteStrings IMPORT WriteString, WriteLn;
  FROM MCPublic IMPORT
    il1File, il2File, ascFile,
    modFile, lstFile, symFile, refFile, objFile,
    Compilerstatus, Statset, compstat,
    comptime, symfileextension;
  FROM MCFileNames IMPORT
    FileName, modName, symName, refName, objName, lstName;
  IMPORT
    SYSTEM;

  CONST
    null = 0C;
    optionlength = 10;

  TYPE
    String = ARRAY [0..19] OF CHAR;
    OptionKind = (nooption,
                  query, noquery,  (* explicit query for symbol files *)
                  list, nolist,    (* generation of a listing file *)
          (*  small, large, *) (**)  (* size of compiled module, work files in memory *)
                  version,         (* display of compiler version *)
                  illegal);
    OptionText = ARRAY [0 .. optionlength-1] OF CHAR;
    Option = RECORD
               minlength : CARDINAL;
               maxlength : CARDINAL;
               text : OptionText;
             END;

  VAR
    compiling : BOOLEAN; (* compiler may run *)
    newtime : Time;
    options : ARRAY OptionKind OF Option;
    qopt, (*mopt,*)(**) lopt, vopt : OptionKind;

  PROCEDURE InitOption(optkind: OptionKind; opttext: OptionText;
                       min, max: CARDINAL);
  BEGIN
    WITH options[optkind] DO
      text := opttext;
      minlength := min;
      maxlength := max;
    END;
  END InitOption;

  PROCEDURE InterpreteOptions(VAR illegaloptions: BOOLEAN);
    VAR opttext : OptionText;
        optlength : CARDINAL;
        optkind : OptionKind;

    PROCEDURE FindOption(VAR opttext: OptionText; optlength: CARDINAL;
                         VAR optkind: OptionKind);
      VAR opk : OptionKind;
          found : BOOLEAN;
          ix : CARDINAL;
    BEGIN
      opk := nooption; INC(opk);
      found := FALSE;
      WHILE NOT found AND (opk < illegal) DO
        WITH options[opk] DO
          IF (minlength<=optlength) AND (optlength<=maxlength) THEN
            ix := 0;
            WHILE (ix < optlength) AND (opttext[ix] = text[ix]) DO
              INC(ix);
            END;
            found := ix = optlength;
          END;
        END;
        IF NOT found THEN INC(opk) END;
      END;
      optkind := opk;
    END FindOption;

  BEGIN (* InterpreteOptions *)
    illegaloptions := FALSE;
    GetOption(opttext,optlength);
    WHILE optlength > 0 DO
      FindOption(opttext,optlength,optkind);
      CASE optkind OF
        query, noquery : qopt := optkind;
   (*    |small, large : mopt := optkind; *)(**)
       |list, nolist : lopt := optkind;
       |version : vopt := optkind;
       |illegal :
          WriteString(" ---- illegal option: ");
          WriteString(opttext);
          WriteLn;
          illegaloptions := TRUE;
      END; (* CASE *)
      GetOption(opttext,optlength);
    END;
  END InterpreteOptions;

  PROCEDURE InitCompilation;

    TYPE DeviceName = ARRAY [0..7] OF CHAR;

    VAR str, extension : String;
        device : DeviceName;
        workdevice : DeviceName;
        illegal : BOOLEAN;
        ok : BOOLEAN;
        ix : CARDINAL;
        idents : CARDINAL;
        extpos : CARDINAL;

    PROCEDURE CreateFile(VAR fnum: CARDINAL; device: DeviceName);
      VAR fp : FilePointer;
          err : BOOLEAN;
    BEGIN
      GetFileNumber(fnum,err);
      GetFileFromPool(fnum,fp,err);
      Create(fp^,device);
      IF fp^.res <> done THEN
        compiling := FALSE;
        WriteString(" ---- file creation failed");
        WriteLn;
        ReturnFileNumber(fnum);
      END;
    END CreateFile;

    PROCEDURE ReturnFile(fnum: CARDINAL);
      VAR fp : FilePointer;
          err : BOOLEAN;
    BEGIN
      GetFileFromPool(fnum,fp,err);
      IF NOT err THEN (* close file *)
        Close(fp^);
        ReturnFileNumber(fnum);
      END;
    END ReturnFile;

    PROCEDURE FixName(ext: ARRAY OF CHAR; VAR fname: FileName);
      VAR ix, pos : CARDINAL;
    BEGIN
      ix := 0;
      pos := extpos;
      fname := modName;
      WHILE (ix <= HIGH(ext)) AND (ext[ix] <> null) AND
            (pos <= HIGH(fname)) DO
        fname[pos] := ext[ix];
        INC(pos);
        INC(ix);
      END;
      IF pos <= HIGH(fname) THEN fname[pos] := null END;
    END FixName;

  BEGIN
    newtime.day := 0;
    newtime.minute := 0;
    newtime.millisecond := 0;
    comptime[0] := 0;
    comptime[1] := 0;
    comptime[2] := 0;
    str := "source file";
    extension := "MOD";
    (* read source file name *)
    LOOP
      (* reset options *)
      qopt := noquery;
  (*    mopt := small; *)(**)
      lopt := nolist; (* list *)(**)
      vopt := nooption;
      (* lookup for source file *)
      LookupFile(str,extension,modFile,TRUE,FALSE,TRUE,modName,ok);
      IF ok THEN
        InterpreteOptions(illegal);
        IF NOT illegal THEN (* test on device and extension *)
          idents := Identifiers(modName);
          IF idents >= 2 THEN
            extpos := IdentifierPosition(modName,idents - 1);
            ix := 0;
            WHILE (ix <= HIGH(device)) AND (modName[ix] <> '.') DO
              device[ix] := modName[ix];
              INC(ix);
            END;
            IF ix <= HIGH(device) THEN device[ix] := 0C END;
     (*     IF (ix <> 2) OR (device[0] <> 'D') OR (device[1] <> 'K') THEN
              illegal := TRUE;
              WriteString(" ---- illegal device");
              WriteLn;
            END; *)(**)
          ELSE
            illegal := TRUE;
            WriteString(" ---- extension missing");
            WriteLn;
          END;
        END;
        IF illegal THEN ReturnFile(modFile);
        ELSE
          compiling := TRUE;
          EXIT;
        END;
      ELSE
        compiling := FALSE;
        WriteString(" ---- no compilation");
        WriteLn;
        EXIT;
      END;
    END; (* LOOP *)
  
    IF compiling THEN
      (* use option information *)
      IF qopt = query THEN INCL(compstat,querys) END;
 (*     IF mopt = small THEN workdevice := "MF" ELSE workdevice := "DK" END; *)(**)
      workdevice := "DK"; (**)
      IF lopt = list THEN INCL(compstat,listings) END;
      IF vopt = version THEN (* display version information *)
        WriteString(" Modula-2 compiler for Lilith");
        WriteLn;
        WriteString(" version EX18 of February 1982");
        WriteLn;
        WriteString(" for system Medos-2 V3");
        WriteLn;
        WriteString(" running under interpreter without memoryfiles"); (**)
        WriteLn;
        WriteString(" does not require file truncation");
        WriteLn;
      END;
      (* create compiler work files *)
      CreateFile(il1File,workdevice); (* interpass file *)
      CreateFile(il2File,workdevice); (* interpass file *)
      CreateFile(ascFile,workdevice); (* identifier table file *)
      (* create generated files *)
      CreateFile(symFile,device); (* symbol file *)
      CreateFile(refFile,device); (* reference file *)
      CreateFile(objFile,device); (* object code file *)
      IF lopt = list THEN CreateFile(lstFile,device) END; (* listing file *)
      (* fix file names of generated files with new extensions *)
      symfileextension := "SYM";
      FixName(symfileextension,symName);
      FixName("REF",refName);
      FixName("OBJ",objName);
      FixName("LST",lstName);
      IF NOT compiling THEN (* return all files *)
        ReturnFile(modFile);
        ReturnFile(il1File);
        ReturnFile(il2File);
        ReturnFile(ascFile);
        ReturnFile(symFile);
        ReturnFile(refFile);
        ReturnFile(objFile);
        IF lopt = list THEN ReturnFile(lstFile) END;
      END;
    END;
  END InitCompilation;

BEGIN (* MCInit *)
  InitOption(query,"QUERY",1,5);
  InitOption(noquery,"NOQUERY",3,7);
(*  InitOption(small,"SMALL",2,5);
  InitOption(large,"LARGE",2,5); *)(**)
  InitOption(list,"LISTING",4,7);
  InitOption(nolist,"NOLISTING",1,9);
  InitOption(version,"VERSION",1,7);
  InitCompilation;
  IF compiling THEN INCL(compstat,compiles) END;
END MCInit.
