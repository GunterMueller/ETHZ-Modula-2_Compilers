(****************************************
*                                       *
*     MODULA-2 Multi-Pass Compiler      *
*     ****************************      *
*                                       *
*     Implementation for Lilith         *
*                                       *
*                                       *
*     MCP2Ident:                        *
*                                       * 
*     Identifier handling in Pass 2     *
*                                       * 
*     Version C18 of 24.02.82           *
*                                       *
*     Institut fuer Informatik          *
*     ETH-Zuerich                       *
*     CH-8092 Zuerich                   *
*                                       *
****************************************)

IMPLEMENTATION MODULE MCP2Ident;   (* LG *)

   (* $T-,R- *)

  FROM MCBase IMPORT Stptr, Structform, Stset;
  IMPORT Storage, MCBase, MCP2IO;

  PROCEDURE FAmong(sp: Stptr; forms: Stset): BOOLEAN;
  BEGIN
    IF sp = NIL THEN RETURN FALSE END;
    WITH sp^ DO
      RETURN (form IN forms) OR
             (form = subranges) AND FAmong(scalp,forms);
    END;
  END FAmong;

  MODULE SearchSystem;

    FROM MCP2IO IMPORT spix;
    FROM MCBase IMPORT
      Idptr, Spellix, Idclass, Structform; 

    EXPORT Search, Locate; 

    PROCEDURE Search(list: Idptr; spix: Spellix; VAR ip: Idptr); 
      (* search in list until found or spix < name *)
    BEGIN
      ip := NIL;
      WHILE list <> NIL DO
        WITH list^ DO
          IF spix > name THEN list := link
          ELSIF spix < name THEN list := NIL
          ELSE (* spix = name *)
            IF klass = indrct THEN ip := nxtidp; (* real entry *)
            ELSE ip := list;
            END;
            list := link; (* find last entry with the same name *)
          END
        END (* WITH *)
      END
    END Search; 

    PROCEDURE Locate(list: Idptr; VAR ip: Idptr);
      (* Search an identifier in list.       *)  
      (* The name spix is taken from MCP2IO. *)
      (* The result (possibly NIL) is        *)
      (* assigned to ip.                     *) 
    BEGIN
      Search(list,spix,ip); (* spix from MCP2IO *)
    END Locate;

  END SearchSystem; 

  MODULE ImpListSystem;

    FROM Storage IMPORT ALLOCATE, DEALLOCATE;
    FROM MCP2IO IMPORT spix, Error;
    FROM MCBase IMPORT
      Idptr, Stptr, Idclass, Structform, Stset,
      Spellix, root, Listptr;
    IMPORT SearchSystem, FAmong;

    EXPORT NewImpList, TermImpList, EnterImpList, ImpSearch;

    VAR implist : Listptr;

    PROCEDURE EnterImpList(ip: Idptr);
      (* enter identifier in import list *)
      VAR newimp : Listptr;
          collision : BOOLEAN;
 
      PROCEDURE OneCheck(spix: Spellix);
        (* check on second import list entry of identifier spix *)
        VAR lip : Idptr;
            imp : Listptr;
      BEGIN
        IF NOT collision THEN
          imp := implist; lip := NIL;
          WHILE (imp <> NIL) AND NOT collision DO
            WITH imp^.element^ DO
              IF name = spix THEN lip := imp^.element;
              ELSIF (klass=mods) AND NOT qualexp THEN
                Search(expp,spix,lip);
              ELSIF (klass=types) AND (idtyp<>NIL) THEN
                IF idtyp^.form=enums THEN
                  Search(idtyp^.fcstp,spix,lip);
                END;
              END;
            END; (* WITH *)
            imp := imp^.next;
            collision := lip <> NIL;
          END; (* WHILE *)
        END;
      END OneCheck;

      PROCEDURE ListCheck(ip: Idptr);
        (* check on second import-list entry of *)
        (* identifiers in list ip               *)
        (* enter also nested modules or         *)
        (* enumeration types in import list     *)
        VAR lip : Idptr;
      BEGIN
        WHILE ip <> NIL DO
          lip := ip;
          IF lip^.klass = indrct THEN lip := lip^.nxtidp END;
          WITH lip^ DO
            IF (klass = mods) AND NOT qualexp THEN EnterImpList(lip);
            ELSIF (klass = types) AND FAmong(idtyp,Stset{enums})THEN
              EnterImpList(lip);
            ELSE OneCheck(name);
            END;
          END; (* WITH *)
          ip := ip^.link;
        END;
      END ListCheck;

    BEGIN
      collision := FALSE;
      WITH ip^ DO
        OneCheck(name);
        IF (klass = mods) AND NOT qualexp THEN ListCheck(expp)
        ELSIF (klass = types) AND (idtyp <> NIL) THEN
          IF idtyp^.form = enums THEN ListCheck(idtyp^.fcstp) END;
        END;
      END;
      IF collision THEN Error(70) END;
      NEW(newimp);
      WITH newimp^ DO element := ip; next := implist END;
      implist := newimp;
    END EnterImpList;

    PROCEDURE ImpSearch(mp: Idptr; VAR ip: Idptr);
      (* search identifier in import list of module mp *)
      VAR imp : Listptr;
          lip : Idptr;
          sp : Stptr;
    BEGIN (* spix from MCP2IO *)
      IF mp <> NIL THEN imp := mp^.impp ELSE imp := NIL END;
      lip := NIL;
      WHILE (lip = NIL) AND (imp <> NIL) DO
        WITH imp^.element^ DO
          IF name = spix THEN
            lip := imp^.element;
          ELSIF (klass = mods) AND NOT qualexp THEN
            Search(expp,spix,lip);
          ELSIF (klass = types) AND FAmong(idtyp,Stset{enums}) THEN
            sp := idtyp;
            IF sp^.form = subranges THEN sp := sp^.scalp END;
            Search(sp^.fcstp,spix,lip);
          END;
        END; (* WITH *)
        imp := imp^.next;
      END; (* WHILE *)
      ip := lip;
    END ImpSearch;

    PROCEDURE NewImpList(imp: Listptr);
      VAR imp1 : Listptr;
    BEGIN
      WHILE imp <> NIL DO (* dispose old import list *)
        imp1 := imp;
        imp := imp^.next;
        DISPOSE(imp1);
      END;
      implist := NIL;
      EnterImpList(root); (* pervasives *)
    END NewImpList;

    PROCEDURE TermImpList(VAR imp: Listptr);
    BEGIN
      imp := implist;
    END TermImpList;

  END ImpListSystem;

  MODULE Scope; 

    FROM Storage IMPORT ALLOCATE, DEALLOCATE;
    FROM MCP2IO IMPORT spix, Error, ErrorLS;
    FROM MCBase IMPORT
      Idclass, Structform, Stset, Idptr,
      Stptr, Spellix, Listptr;
    IMPORT SearchSystem, ImpListSystem, FAmong; 

    EXPORT
      EnterList, EnterId, EnterForward,
      SearchId, ExportSearch, SymModSearch,
      GlobalKnown,
      MsEntry, SearchInBlock, MarkScope, ReleaseScope;

    CONST maxscope = 15;

    TYPE Scoperange = [0 .. maxscope];
         Forwardptr = POINTER TO Forwardrec;
         Forwardrec = RECORD
                        next : Forwardptr;
                        fwname : Spellix;
                        ptrtp : Stptr;
                      END;

    VAR displ : ARRAY Scoperange OF 
                  RECORD
                    localp : Idptr;       (* objects declared for local use *)
                    extendp : Listptr;    (* objects with extended scope *)
                    exportp : Idptr;      (* objects declared for export *)
                    modulep : Idptr;      (* entry of a module *)
                    forwardp : Forwardptr;(* pointers with forward types *)
                  END;
        level: CARDINAL;       (* current level, may exceed maxscope *)

    PROCEDURE EnterList(VAR rf: Idptr; fip: Idptr);
      VAR lip,lip1: Idptr; nam: Spellix;
    BEGIN 
      (* insert in ordered list *)
      nam := fip^.name; 
      lip := rf;
      WHILE (lip <> NIL) AND (lip^.name <= nam) DO
        IF lip^.name = nam THEN Error(72) END;
        lip1 := lip;
        lip := lip1^.link;
      END;
      fip^.link := lip; 
      IF lip = rf THEN rf := fip ELSE lip1^.link := fip END;
    END EnterList; 
  
    PROCEDURE SearchInBlock(VAR ip: Idptr);
      VAR ls : Listptr; 
    BEGIN (* spix from MCP2IO *)
      IF level <= maxscope THEN
        WITH displ[level] DO
          Search(localp,spix,ip);
          IF ip = NIL THEN
            ls := extendp; 
            WHILE (ls <> NIL) AND (ip = NIL) DO
              WITH ls^ DO Search(element,spix,ip); ls := next END 
            END 
          END;
          IF (ip = NIL) AND (modulep <> NIL) THEN (* module block *)
            ImpSearch(modulep,ip);
            IF ip = NIL THEN Search(exportp,spix,ip) END; 
            (* possibly unknown entry in export list *)
          END;
        END; (* WITH *)
      ELSE ip := NIL;
      END;
    END SearchInBlock;

    PROCEDURE EnterId(ip: Idptr);
      VAR y: Idptr; 
    BEGIN 
      IF level <= maxscope THEN
        SearchInBlock(y);
        IF y = NIL THEN EnterList(displ[level].localp,ip)
        ELSIF y^.klass = unknown THEN (* replace export-list entry *)
          WITH y^ DO
            ip^.link := link; 
            IF (link <> NIL) AND (link^.klass = unknown) THEN 
              link^.nxtidp := ip;
            END;
            WITH nxtidp^ DO (* is guaranteed to be <> NIL *)
              IF (klass=mods) AND (expp=y) THEN
                (* identifier is first element in exportlist *) 
                displ[level].exportp := ip; expp := ip; 
              ELSE
                link := ip;
              END; 
            END;
          END;
          DISPOSE(y,unknown); 
        ELSE Error(72); EnterList(displ[level].localp,ip)
        END;
      END;
    END EnterId;

    PROCEDURE EnterForward(ptrtype: Stptr);
      VAR lfp : Forwardptr;
    BEGIN
      IF level <= maxscope THEN
        NEW(lfp);
        WITH lfp^DO
          next := displ[level].forwardp;
          fwname := spix; (* from MCP2IO *)
          ptrtp := ptrtype;
        END;
        displ[level].forwardp := lfp;
      END;
    END EnterForward;

    PROCEDURE UpdateForwards;
      VAR updatefail : BOOLEAN;
          lfp, lfp1 : Forwardptr;
          oldspix : Spellix;
          ip : Idptr;
    BEGIN
      IF level <= maxscope THEN
        updatefail := FALSE;
        oldspix := spix; (* save current spix *)
        lfp := displ[level].forwardp;
        WHILE lfp <> NIL DO
          WITH lfp^DO
            spix := fwname;
            SearchId(ip);
            IF (ip = NIL) OR (ip^.klass <> types) THEN
              updatefail := TRUE;
            ELSE
              ptrtp^.elemp := ip^.idtyp;
            END;
            lfp1 := lfp;
            lfp := next;
          END;
          DISPOSE(lfp1);
        END;
        spix := oldspix;
        IF updatefail THEN ErrorLS(90) END;
      END;
    END UpdateForwards;

    PROCEDURE SearchId(VAR ip: Idptr);
      VAR ls : Listptr;
          clev : Scoperange;
      (* Search an identifier in the current scope. *)
      (* The name spix is taken from MCP2IO.        *)
    BEGIN
      ip := NIL;
      IF level <= maxscope THEN
        clev := level;
        LOOP
          WITH displ[clev] DO
            Search(localp,spix,ip);
            IF ip = NIL THEN
              ls := extendp; 
              WHILE (ls <> NIL) AND (ip = NIL) DO
                Search(ls^.element,spix,ip); ls := ls^.next;
              END;
            END;
            IF (ip<>NIL) OR (modulep<>NIL) THEN EXIT END; (* found or on module level *)
          END; (* WITH *)
          DEC(clev);
        END;
        IF ip = NIL THEN Search(displ[clev].exportp,spix,ip) END;
        IF ip = NIL THEN ImpSearch(displ[clev].modulep,ip) END;
      END;
    END SearchId;

    PROCEDURE ExportSearch(ep: Idptr; VAR ip: Idptr);
      (* Search an identifier in the         *)
      (* export list of a module.            *)
      (* The name spix is taken from MCP2IO. *)
      VAR lip : Idptr; 
          lep : Idptr; 
          sp : Stptr; 
    BEGIN (* spix from MCP2IO *)
      Search(ep,spix,lip); 
      IF lip = NIL THEN (*search in enumeration type or nested module*) 
        WHILE (lip = NIL) AND (ep <> NIL) DO 
          lep := ep;   
          IF lep^.klass = indrct THEN lep := lep^.nxtidp END; 
          WITH lep^ DO   
            IF (klass = mods) AND NOT qualexp THEN
              ExportSearch(expp,lip);  
            ELSIF (klass = types) AND FAmong(idtyp,Stset{enums}) THEN 
              sp := idtyp; 
              IF sp^.form = subranges THEN sp := sp^.scalp END;  
              Search(sp^.fcstp,spix,lip)
            END; 
          END; (* WITH *) 
        ep := ep^.link; 
        END; (* WHILE *) 
      END; 
      ip := lip;
    END ExportSearch;

    PROCEDURE SymModSearch(VAR ip: Idptr);
      (* search identifier belonging to symbol module *)
    BEGIN (* spix from MCP2IO *)
      ip := NIL;
      IF level <= maxscope THEN
        Search(displ[level].exportp,spix,ip);
        IF ip = NIL THEN Search(displ[level].localp,spix,ip);
        ELSIF ip^.klass = unknown THEN ip := NIL;
        END;
      END;
    END SymModSearch;

    PROCEDURE GlobalKnown(spx: Spellix): BOOLEAN;
      (* check name spx for possible implementation *)
      (* i.e. it must be known at global level of   *)
      (* an implementation module; the name may be  *)        
      (* exported from a nested module              *)
      VAR clev : Scoperange;
          x : Idptr;
          stack : ARRAY [0..9] OF Spellix; (* possibly exported names *)
          ind, high : [0..10];
    BEGIN (* assume nested modules only *)
      IF level > maxscope THEN RETURN FALSE END;
      high := 0; 
      clev := level; (* level of exportlist *)
      WHILE clev > 1 DO (* do not search on global level *)
        WITH displ[clev] DO 
          IF modulep^.qualexp THEN RETURN FALSE END; 
          Search(exportp,spx,x); (* search spx in exportlist *) 
          IF x = NIL THEN (* search elements from stack *) 
            ind := 0; 
            WHILE ind < high DO   
              Search(exportp,stack[ind],x); 
              INC(ind); 
              IF x <> NIL THEN high := ind END; 
            END; 
            IF x = NIL THEN RETURN FALSE END; (* not global known *) 
          ELSE (* enter spx in stack *)  
            stack[high] := spx;  
            INC(high);   
          END; 
          spx := modulep^.name; (* module name is possibly exported *) 
        END; 
        DEC(clev); 
      END; 
      RETURN TRUE 
    END GlobalKnown; 

    PROCEDURE NewLevel(locp: Idptr; extp: Listptr; expp, modp: Idptr);
    BEGIN
      INC(level);
      IF level <= maxscope THEN
        WITH displ[level] DO
          localp := locp;
          extendp := extp;
          exportp := expp;
          modulep := modp;
          forwardp := NIL;
        END;
      ELSE ErrorLS(79);
      END;
    END NewLevel;

    PROCEDURE OldLevel(VAR locp: Idptr; VAR extp: Listptr);
    BEGIN
      IF level <= maxscope THEN
        WITH displ[level] DO
          locp := localp;
          extp := extendp;
        END; (* WITH *)
      END;
      DEC(level);
    END OldLevel;

    PROCEDURE MarkScope(ip : Idptr);
    BEGIN
      WITH ip^ DO
        IF klass = mods THEN
          NewLevel(locp,msp,expp,ip);
        ELSE
          NewLevel(locp,msp,NIL,NIL);
        END;
      END; (* WITH *)
    END MarkScope; 

    PROCEDURE ReleaseScope(ip: Idptr); 
    BEGIN
      UpdateForwards;
      WITH ip^ DO
        OldLevel(locp,msp);
      END; (* WITH *)
    END ReleaseScope;

    PROCEDURE ExtendEntry(fip: Idptr);
      (* enter identifier list into the extend list of the current scope *)
      VAR lp : Listptr;
          ip : Idptr;
          savespix : Spellix;
          (* spix from MCP2IO *)
    BEGIN (* ExtendEntry *)
      IF (fip <> NIL) AND (level <= maxscope) THEN
        (* create extend list element *)
        NEW(lp);
        WITH lp^ DO element := fip; next := NIL END;
        (* check on name conflicts in scope and on indirect exports *)
        savespix := spix;
        WHILE fip <> NIL DO
          spix := fip^.name;
          SearchInBlock(ip);
          IF ip <> NIL THEN
            WITH ip^ DO
              IF klass = unknown THEN
                klass := indrct;
                IF fip^.klass = indrct THEN nxtidp := fip^.nxtidp;
                ELSE nxtidp := fip;
                END
              ELSE ErrorLS(85);
              END;
            END; (* WITH *)
          END;
          fip := fip^.link;
        END; (* WHILE *)
        spix := savespix;
        (* entry into extend list *)
        WITH displ[level] DO
          lp^.next := extendp;
          extendp := lp;
        END; (* WITH *)
      END;
    END ExtendEntry;

    PROCEDURE MsEntry(fip: Idptr);
    BEGIN
      ExtendEntry(fip);
    END MsEntry;

(*
    PROCEDURE MsEntry(fip: Idptr);
      VAR lp : Listptr;
          ip : Idptr;
    BEGIN
      IF (fip <> NIL) AND (level <= maxscope) THEN
        WITH displ[level] DO
          (* entry in displ *)
          NEW(lp);
          WITH lp^ DO element := fip; next := extendp END;
          extendp := lp;
          (* check indirect exports on export-list *)
          IF exportp <> NIL THEN
            WHILE fip <> NIL DO 
              Search(exportp,fip^.name,ip);
              IF ip <> NIL THEN
                WITH ip^ DO
                  IF klass = unknown THEN
                    klass := indrct;
                    IF fip^.klass = indrct THEN nxtidp := fip^.nxtidp;
                    ELSE nxtidp := fip;
                    END
                  ELSE Error(72);
                  END;
                END; (* WITH *)
              END;
              fip := fip^.link;
            END; (* WHILE *)
          END;
        END; (* WITH *)
      END;
    END MsEntry;
*)

  BEGIN (* Scope *)
    level := 0;
    WITH displ[level] DO
      localp := NIL;
      extendp := NIL;
      exportp := NIL;
      modulep := NIL;
      forwardp := NIL;
    END;
  END Scope;

END MCP2Ident.
