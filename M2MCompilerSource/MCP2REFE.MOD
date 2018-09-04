(****************************************
*                                       *
*     MODULA-2 Multi-Pass Compiler      *
*     ****************************      *
*                                       *
*     Implementation for Lilith         *
*                                       *
*                                       *
*     MCP2Reference:                    *
*                                       * 
*     Generation of reference file      *
*                                       * 
*     Version C18 of 08.04.81           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

IMPLEMENTATION MODULE MCP2Reference; (* AV / LG *)

  (* $T-,R- *)

  FROM NewStreams IMPORT
    STREAM, Connect, Reset, WriteWord, EndWrite, Disconnect;
  FROM MCP2IO  IMPORT line, AsciiSetPos, AsciiRead, maxspix;
  FROM MCBase IMPORT
    Idptr, Stptr, Idclass, Structform, Varkind, Kindvar, Spellix;
  FROM MCPublic IMPORT refFile;

  TYPE
    RefSymbol =
      (Mod, Proc, Var,
       Int, Card, Char, Bool, Word, Real,
       Arr, ArrDyn, Rec, Point, Set, Scal, Procvar, Hide,
       Abs, Ind, Rel, End, Undef);
    Byte = [0..377B];

  VAR
    ref     : STREAM;
    writeref: BOOLEAN; (* writing on ref file allowed *)
    wordbuff : CARDINAL;
    highbyte : BOOLEAN;
        
  PROCEDURE WriteRef(b: Byte);
  BEGIN
    (* format to 0..377B *)
    b := b MOD 400B;
    IF highbyte THEN
      INC(wordbuff,b*400B);
      WriteWord(ref,wordbuff);
    ELSE
      wordbuff := b;
    END;
    highbyte := NOT highbyte;
  END WriteRef;

  PROCEDURE RefSym ( sym : RefSymbol );
    (* write a Refsymbol on the ref file *)
  BEGIN
    WriteRef(ORD(sym)) 
  END RefSym;

  PROCEDURE RefIdent(spix:Spellix);
    VAR ch: CHAR;
  BEGIN
    IF spix>maxspix THEN WriteRef(ORD("*"));
    ELSE
      AsciiSetPos(spix);
      AsciiRead(ch);
      WHILE ch <> ' ' DO 
        WriteRef(ORD(ch));
        AsciiRead(ch);
      END;
    END(*else*);
    WriteRef(0);
  END RefIdent;
  
  PROCEDURE RefNum ( num : CARDINAL );
    (* write a number on the ref file *)
  BEGIN
    WriteRef(num DIV 400B);
    WriteRef(num MOD 400B);
  END RefNum;

  PROCEDURE Reference ( ip : Idptr );
    (* write a reference to the identifier *)
    VAR tp : Stptr; 
        sym : RefSymbol;
  BEGIN
    IF writeref AND (ip<>NIL) THEN
      WITH ip^ DO
        CASE klass OF
          mods : RefSym (Mod);
                 RefNum (line);
                 RefIdent (name);
                 RefNum (procnum);
         |pures,funcs :
                 RefSym (Proc);
                 RefNum (line);
                 RefIdent (name);
                 RefNum (procnum);
         |vars : RefSym (Var);
                 RefNum (line);
                 RefIdent (name);
                 tp := idtyp;
                 IF (tp <> NIL) AND (tp^.form = subranges) THEN  
                   tp := tp^.scalp; 
                 END; 
                 IF tp<>NIL THEN
                   WITH tp^ DO
                     CASE form OF
                       ints     : sym := Int;
                      |cards    : sym := Card;
                      |bools    : sym := Bool;
                      |chars    : sym := Char;
                      |words    : sym := Word;
                      |reals    : sym := Real;
                      |arrays   :
                         IF dyn THEN sym := ArrDyn;
                         ELSE sym := Arr;
                         END;
                      |records  : sym := Rec;
                      |pointers : sym := Point;
                      |sets     : sym := Set;
                      |enums    : sym := Scal;
                      |proctypes: sym := Procvar;
                      |hides    : sym := Hide;
                     ELSE sym := Undef
                     END (* case *);
                   END(*with*);
                 ELSE sym := Undef;
                 END;
                 RefSym(sym);
                 IF state = absolute THEN RefSym(Abs) 
                 ELSE 
                   IF indaccess THEN RefSym(Ind)
                   ELSE RefSym(Rel)
                   END
                 END;
                 RefNum(vaddr);
                 IF tp <> NIL THEN RefNum(tp^.size);
                 ELSE RefNum(0);      
                 END;                
             ELSE
         END (*case*)
       END (*with*)
     END;
  END Reference;

  PROCEDURE EndReference(ip:Idptr);
  BEGIN
    IF writeref AND (ip<>NIL) THEN RefSym(End) END;
  END EndReference;

  PROCEDURE InitRef;
    (* initialisation of ref file *)
  BEGIN (*InitRef*)
    writeref := TRUE;
    Connect(ref,refFile,TRUE);
    highbyte := FALSE;
    Reset(ref);
  END InitRef;

  PROCEDURE TermRef;
  BEGIN
    IF highbyte THEN WriteRef(0) END;
    EndWrite(ref);
    Disconnect(ref,FALSE);
    writeref := FALSE;
  END TermRef;

BEGIN (* MCP2Reference *)
  writeref := FALSE
END MCP2Reference. 
