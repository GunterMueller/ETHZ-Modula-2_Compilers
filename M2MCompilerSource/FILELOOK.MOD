IMPLEMENTATION MODULE FileLookup;    (* LG 06.11.81 *)
  (* $T- *)
  (* version for Personal Computer *)

  FROM FileSystem IMPORT Response, Lookup, Close;
  FROM FilePool IMPORT
    FilePointer, GetFileNumber, GetFileFromPool, ReturnFileNumber;
  FROM Options IMPORT FileNameAndOptions, Termination;
  FROM Terminal IMPORT Write, WriteString, WriteLn;

  CONST null = 0C;  (* null character *)

  PROCEDURE LookupFile(name: ARRAY OF CHAR;
                       defaultextension: ARRAY OF CHAR;
                       VAR filenum: CARDINAL;
                       query, acceptdefault, acceptoptions: BOOLEAN;
                       VAR acceptedfilename: ARRAY OF CHAR;
                       VAR goodfile: BOOLEAN);

    (* name          : the name is displayed and a default *)
    (*                 file name is constructed from name *)
    (* filenum       : file number is assigned from FilePool *)
    (* query         : explicit asking for file name *)
    (* acceptdefault : accept a default file name *)
    (* acceptoptions : accept options appended to file name *)
    (*                 options are not evaluated *)
    (* goodfile      : lookup was successfull *)

    CONST namelength = 32;

    TYPE Text = ARRAY [0..15] OF CHAR;
         FileName = ARRAY [0 .. namelength - 1] OF CHAR;

    VAR dname,fname : FileName;
        termstat : Termination;
        ix, hix : CARDINAL;
        searching : BOOLEAN;
        cancel : BOOLEAN;
        lookup, default : BOOLEAN;
        fp : FilePointer;
        err : BOOLEAN;

    PROCEDURE ErrorMessage(mess: Text);
    BEGIN
      WriteLn;
      WriteString("  ---- ");
      WriteString(mess);
    END ErrorMessage;

  BEGIN
    (* initialisation *)
    searching := TRUE;
    goodfile := FALSE;
    (* generate default filename *)
    ix := 0;
    IF acceptdefault THEN
      hix := 0;
      WHILE (hix < 16) AND (hix <= HIGH(name)) AND (name[hix] <> null) DO
        dname[ix] := name[hix];
        INC(hix);
        INC(ix);
      END;
    END;
    dname[ix] := "."; INC(ix);
    hix := 0;
    WHILE (ix <= HIGH(dname)) AND (hix <= HIGH(defaultextension)) AND
          (defaultextension[hix] <> null) DO
      dname[ix] := defaultextension[hix];
      INC(ix); INC(hix);
    END;
    WHILE ix <= HIGH(dname) DO dname[ix] := null; INC(ix) END;
    (* get file *)
    GetFileNumber(filenum,err);
    IF NOT err THEN GetFileFromPool(filenum,fp,err) END;
    IF err THEN
      ErrorMessage("no file in pool");
      searching := FALSE;
    END;
    (* search file *)
    WHILE searching DO
      Write(' '); 
      WriteString(name);
      lookup := FALSE;
      IF query THEN
        Write('>'); Write(' ');
        FileNameAndOptions(dname,fname,termstat,acceptoptions);
        IF termstat = normal THEN
          lookup := TRUE; default := FALSE;
        ELSIF termstat = esc THEN
          searching := FALSE;
        ELSIF termstat = empty THEN
          IF acceptdefault THEN 
            lookup := TRUE; default := TRUE;
            fname := dname;
          ELSE
            ErrorMessage("no default file");
          END;
        END;
      ELSE (* NOT query *)
        Write(':'); Write(' ');
        lookup := TRUE; default := TRUE;
        fname := dname;
        searching := FALSE; (* go ahead when file not found *)
      END;
      IF lookup THEN
        IF default THEN
          fname := dname;
        END;
        Lookup(fp^,fname,FALSE);
        IF default AND (fp^.res <> done) THEN
          fname := "LIB.";
          ix := 4; hix := 0;
          WHILE ix <= HIGH(fname) DO
            fname[ix] := dname[hix];
            INC(ix); INC(hix);
          END;
          Lookup(fp^,fname,FALSE);
        END;
        IF fp^.res = done THEN (* file found *)
          IF default THEN (* write file name *)
            WriteString(fname);
          END;
          goodfile := TRUE;
          searching := FALSE;
        ELSE
          IF default THEN ErrorMessage("no file found");
          ELSE ErrorMessage("file not found");
          END;
        END;
      END;
      WriteLn;
    END;  (* WHILE *)
    IF goodfile THEN
      ix := 0;
      WHILE (ix <= HIGH(fname)) AND (ix <= HIGH(acceptedfilename)) DO
        acceptedfilename[ix] := fname[ix];
        INC(ix);
      END;
      IF ix <= HIGH(acceptedfilename) THEN
        acceptedfilename[ix] := null;
      END;
    ELSE
      ReturnFileNumber(filenum);
    END;
  END LookupFile;   

  (* $T= *)
END FileLookup.
