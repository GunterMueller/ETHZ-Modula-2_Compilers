(* has modifications in it for use without memoryfiles *)
(* also does not put C18 on front of calls *)
(* also has modifications to use the Q-lister *)
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
*     MCPublic:                         *
*                                       * 
*     public part of the common base    *
*     of the Modula-2 compiler          *
*                                       * 
*     Version C18 of 04.06.81           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

IMPLEMENTATION MODULE MCPublic;   (* LG *)

  IMPORT Storage (* for initialisation of storage procedures *),
         NewStreams (* for initialisation of module streams *)(*,
         MemoryFiles (* for initialisation of memory files *) *)(**);

  FROM Program IMPORT Status, Call; 
  FROM ProgramMessage IMPORT WriteStatus;
  FROM FileSystem IMPORT
    File, Response, Lookup, Rename, Close;
  FROM FilePool IMPORT FilePointer, GetFileFromPool, ReturnFileNumber;
  FROM WriteStrings IMPORT WriteString, WriteLn;
  FROM MCFileNames IMPORT FileName, symName, refName, objName, lstName;

  TYPE
    Passes = (pass1,pass2,pass3,pass4,lister,terminate);

  VAR
    dummyName : FileName;
    passindicator: Passes;
    exerror : Status;
    message : ARRAY [0..9] OF CHAR;
    filenam : FileName;
  
  PROCEDURE Terminate(VAR fnum: CARDINAL; VAR fname: FileName;
                      newfile: BOOLEAN);
    VAR
      old : File;
      f : FilePointer;
      err : BOOLEAN;
  BEGIN
    GetFileFromPool(fnum,f,err);
    IF newfile AND NOT err THEN (* lookup for old file *)
      Lookup(old,fname,FALSE);
      IF old.res = done THEN (* purge old file *)
        Rename(old,"");
        Close(old);
      END;
      Rename(f^,fname);
    END;
    IF err OR newfile AND (f^.res <> done) THEN
      WriteString(" ---- not catalogued : ");
      WriteString(fname);
      WriteLn;
    END;
    IF NOT err THEN
      Close(f^);
      ReturnFileNumber(fnum);
    END;
  END Terminate;

BEGIN (* MCPublic *)
  compstat := Statset{};
  Call("Init",TRUE,exerror);
  IF exerror <> normal THEN
    WriteStatus(exerror);
  ELSIF compiles IN compstat THEN (* compilation *)
    passindicator := pass1;     
    LOOP
      CASE passindicator OF
        pass1:
          message := "p1";
          filenam := "Pass1";             
       |pass2:
          message := "p2";
          filenam := "Pass2"; 
       |pass3:
          IF defs IN compstat THEN
            IF globerrs IN compstat THEN (* listing generation *)
              IF listings IN compstat THEN
                message := "lister";
                filenam := "Lister"; 
                passindicator := terminate;
              ELSE
                message := "q-lister";(**)
                filenam := "QLister";(**)
                passindicator := terminate;(**)
                (*EXIT*)(**)
              END;
            ELSE (* symbol file generation *)
              message := "symfile";
              filenam := "Symfile"; 
            END;
          ELSE
            message := "p3";
            filenam := "Pass3"; 
          END;
       |pass4:
          IF (globerrs IN compstat) OR (defs IN compstat) THEN (* listing *)
            IF listings IN compstat THEN
              message := "lister";
              filenam := "Lister"; 
              passindicator := terminate;
            ELSIF globerrs IN compstat THEN (**)
              message := "q-lister";(**)
              filenam := "QLister";(**)
              passindicator := terminate;(**)
            ELSE EXIT
            END;
          ELSE
            message := "p4";
            filenam := "Pass4"; 
          END;
       |lister:
          IF listings IN compstat THEN
            message := "lister";
            INCL(compstat,finis);
            filenam := "Lister"; 
            passindicator := terminate;
          ELSIF globerrs IN compstat THEN (**)
            message := "q-lister";(**)
            INCL(compstat,finis);(**)
            filenam := "QLister"; (**)
            passindicator := terminate;(**)
          ELSE EXIT
          END;
      END; (* CASE *)
      WriteString(message);
      WriteLn;
      Call(filenam,TRUE,exerror);
      IF exerror = normal THEN (* Call executed *)
        IF symerrs IN compstat THEN (* stop compilation *)
          WriteString(" ---- symbolfiles missing");
          WriteLn;
          EXCL(compstat,compiles);
          EXIT;
        END;
        IF passerrs IN compstat THEN (* error handling *) 
          INCL(compstat,globerrs); 
          WriteString(" ---- error"); 
          WriteLn;
        END; 
        IF passindicator = terminate THEN EXIT END;
        EXCL(compstat,passerrs); 
        INC(passindicator); 
      ELSE (* cancel execution *)
        WriteString(" ----");
        WriteStatus(exerror);
        WriteLn;
        EXCL(compstat,compiles);
        EXIT;
      END; 
    END; (* LOOP *)  
    (* termination *)   
    Terminate(il1File,dummyName,FALSE);
    Terminate(il2File,dummyName,FALSE);
    Terminate(ascFile,dummyName,FALSE);
    Terminate(modFile,dummyName,FALSE);
    Terminate(refFile,refName,
      compstat*Statset{globerrs,defs,compiles}=Statset{compiles});
    Terminate(objFile,objName,
      compstat*Statset{globerrs,defs,compiles}=Statset{compiles});
    Terminate(symFile,symName,
      compstat*Statset{globerrs,syms,compiles}=Statset{syms,compiles});
    IF listings IN compstat THEN
      Terminate(lstFile,lstName,compiles IN compstat);
    END;
    WriteString("end compilation");
    WriteLn;
  END;
END MCPublic.
