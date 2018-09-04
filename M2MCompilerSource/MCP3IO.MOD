(****************************************
*                                       *
*     MODULA-2 Multi-Pass Compiler      *
*     ****************************      *
*                                       *
*     Implementation for Lilith         *
*                                       *
*                                       *
*     MCP3IO:                           *
*                                       * 
*     input / output handling in Pass 3 *
*                                       * 
*     Version C18 of 09.03.81           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

IMPLEMENTATION MODULE MCP3IO;    (* LG *)

  (* $T-,R- *)

  IMPORT SYSTEM, NewStreams, Storage, MCBase, MCPublic;

  (* declarations in definition module

  TYPE Savepos;

  VAR sy : Symbol;
      val : CARDINAL;    (* value *)
      length : CARDINAL; (* string length *)
      spix : Spellix;    (* spelling index of identifier *)
      nptr : Idptr;      (* pointer to referenced name *)

  end declarations *)

  VAR pos, line, lpos, lline : CARDINAL;

  MODULE OutputSystem;
 
    FROM SYSTEM IMPORT WORD;
    FROM Storage IMPORT ALLOCATE, DEALLOCATE;
    FROM NewStreams IMPORT
      STREAM, Connect, Reset, WriteWord, EndWrite, Disconnect,
      GetPos, SetPos;
    FROM MCBase IMPORT Symbol;
    FROM MCPublic IMPORT il1File;
    IMPORT pos, line;
 
    EXPORT
      PutSy, PutWord, TermOutput,
      Savepos, InitSave, ResetSave, ReleaseSave;
 
    TYPE Savepos = CARDINAL;
         Symptr = POINTER TO Symrec;
         Symrec = RECORD
                    next : Symptr;
                    elem : WORD;
                  END;
         Remptr = POINTER TO Remrec;
         Remrec = RECORD
                    next : Remptr;
                    sympos : Symptr;
                    save : Savepos;
                  END;

    VAR il1 : STREAM;
        symhead, symtail : Symptr;
        remhead, remtail : Remptr;
        savelevel : CARDINAL;
        remcnt : CARDINAL;
        saving : BOOLEAN;
        remaining : BOOLEAN;

    PROCEDURE SaveWord(w: WORD);
    BEGIN
      WITH symtail^ DO
        elem := w;
        IF next = NIL THEN NEW(next); next^.next := NIL END;
        symtail := next;
      END;
      DEC(remcnt);
      IF remcnt = 0 THEN remaining := FALSE END;
    END SaveWord;

    PROCEDURE PutSy(sy: Symbol);
      (* put symbol sy on output stream *)
      VAR w : WORD;
    BEGIN
      w := WORD(ORD(sy) * 400B + pos);
      IF saving THEN
        CASE sy OF
          eol, errorsy : remcnt := 2;
         |option : remcnt := 3;
        ELSE remcnt := 0;
        END;
        remaining := remcnt > 0;
        IF remaining THEN  SetRemaining; SaveWord(w) END;
      END;
      WriteWord(il1,w);
    END PutSy;

    PROCEDURE PutWord(w: WORD);
      (* put word w on output stream *)
    BEGIN
      IF remaining THEN SaveWord(w) END;
      WriteWord(il1,w);
    END PutWord;

    PROCEDURE SetRemaining; 
      VAR dummy : CARDINAL;
    BEGIN 
      WITH remtail^ DO 
        sympos := symtail; 
        GetPos(il1,dummy,save);
        IF dummy <> 0 THEN HALT END;
        IF next = NIL THEN NEW(next); next^.next := NIL END; 
        remtail := next;
      END;
    END SetRemaining;

    PROCEDURE ResetRemainings(s : Savepos);
      VAR sym : Symptr;
          r: Remptr;
          sy : Symbol;
          dummy : CARDINAL;
          cnt : CARDINAL;
    BEGIN
      r := remhead;
      WHILE (r <> remtail) AND (r^.save < s) DO r := r^.next END;
      WHILE r <> remtail DO
        WITH r^ DO
          sym := sympos;
          GetPos(il1,dummy,save);
          IF dummy <> 0 THEN HALT END;
          r := next;
        END;
        sy := VAL(Symbol,CARDINAL(sym^.elem) DIV 400B);
        IF sy = option THEN cnt := 3 ELSE cnt := 2 END;
        WHILE cnt > 0 DO
          PutWord(sym^.elem);
          DEC(cnt);
          sym := sym^.next;
        END;
      END;   
    END ResetRemainings;
 
    PROCEDURE InitSave(VAR s: Savepos);
      VAR dummy : CARDINAL;
    BEGIN
      IF saving THEN
        INC(savelevel);
      ELSE
        saving := TRUE;
        symtail := symhead;
        remtail := remhead;
        savelevel := 0;
      END;
      GetPos(il1,dummy,s);
      IF dummy <> 0 THEN HALT END;
    END InitSave;

    PROCEDURE ResetSave(s: Savepos);
    BEGIN
      SetPos(il1,0,s);
      ResetRemainings(s);
    END ResetSave;     

    PROCEDURE ReleaseSave(s: Savepos);
    BEGIN
      IF savelevel = 0 THEN saving := FALSE;
      ELSE DEC(savelevel);
      END;
    END ReleaseSave;

    PROCEDURE TermOutput;
    BEGIN
      WHILE symhead <> NIL DO
        symtail := symhead; 
        symhead := symhead^.next; 
        DISPOSE(symtail); 
      END; 
      WHILE remhead <> NIL DO
        remtail := remhead;
        remhead := remhead^.next;
        DISPOSE(remtail);
      END;
      PutSy(eop);
      EndWrite(il1); Disconnect(il1,FALSE);
    END TermOutput;

  BEGIN
    NEW(symhead);
    symhead^.next := NIL;
    NEW(remhead);
    remhead^.next := NIL;
    saving := FALSE;
    remaining := FALSE;
    Connect(il1,il1File,TRUE); Reset(il1);
  END OutputSystem;

  MODULE ErrorSystem;

    FROM MCBase IMPORT Symbol;
    FROM MCPublic IMPORT Compilerstatus, compstat;
    FROM OutputSystem IMPORT PutSy, PutWord;
    IMPORT line, pos, lline, lpos;

    EXPORT Error,ErrorLS;

    CONST errmax = 300;

    VAR errcount : CARDINAL;

    PROCEDURE Error(n : CARDINAL);
    BEGIN INC(errcount); INCL(compstat,passerrs);
      IF errcount < errmax THEN
        PutSy(errorsy); PutWord(n);
      ELSIF errcount = errmax THEN
        PutSy(errorsy); PutWord(5); (* too many errors *) 
      END;
    END Error;

    PROCEDURE ErrorLS(n : CARDINAL);
      VAR hpos : CARDINAL;
    BEGIN 
      hpos := pos; pos := lpos;
      IF lline <> line THEN
        PutSy(eol); PutWord(lline);
        Error(n);
        PutSy(eol); PutWord(line);
      ELSE Error(n);
      END;
      pos := hpos;
    END ErrorLS;

  BEGIN
    errcount := 0; EXCL(compstat,passerrs);
  END ErrorSystem;

  MODULE Scanner;

    FROM NewStreams IMPORT
      STREAM, Connect, ReadWord, WriteWord, Reset, Disconnect;
    FROM MCBase IMPORT Idptr, Spellix, Symbol;
    FROM MCPublic IMPORT il2File;
    FROM OutputSystem IMPORT PutSy, PutWord;
    IMPORT
      sy, val, length, spix, nptr,
      pos, line, lpos, lline;

    EXPORT GetSy, PutGetSy, TermInput;

    VAR
      card : CARDINAL;
      il2 : STREAM; 
      issy : BOOLEAN;

    PROCEDURE GetSy;
    BEGIN (* get next symbol *)
      lpos := pos; lline := line; 
      REPEAT
        issy := TRUE; 
        ReadWord(il2,card);
        pos := card MOD 400B;
        sy := VAL(Symbol,card DIV 400B);
        CASE sy OF
          ident: ReadWord(il2,spix);
         |namesy,proceduresy,modulesy,symbolsy,definitionsy:
            ReadWord(il2,nptr);
         |intcon,cardcon,intcarcon,charcon,realcon: ReadWord(il2,val);
         |stringcon: ReadWord(il2,val); ReadWord(il2,length);
         |option:
            ReadWord(il2,val);
            ReadWord(il2,card);
            PutSy(sy);
            PutWord(val); PutWord(card);
            issy := FALSE;
         |errorsy,eol:
            ReadWord(il2,val);
            IF sy = eol THEN line := val END;
            PutSy(sy);
            PutWord(val);
            issy := FALSE;
        ELSE (* no activity *)
        END; (* CASE *)
      UNTIL issy;
    END GetSy;

    PROCEDURE PutGetSy;
    BEGIN (* put last Symbol, get next Symbol *)
      PutSy(sy);
      CASE sy OF
        ident: PutWord(spix);
       |namesy,proceduresy,modulesy: PutWord(nptr);
       |intcon,cardcon,intcarcon: PutWord(val);
      ELSE (* no activity *)
      END; (* CASE *)
      GetSy;
    END PutGetSy;

    PROCEDURE TermInput;
    BEGIN Disconnect(il2,FALSE);
    END TermInput;

  BEGIN
    Connect(il2,il2File,TRUE); Reset(il2);
    line := 1;
  END Scanner;

  PROCEDURE TermInOut;
  BEGIN
    TermInput;
    TermOutput;
  END TermInOut;

END MCP3IO.
