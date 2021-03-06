IMPLEMENTATION MODULE FPUControl; (* HS 11.9.91 / 29.5.92 *)
  FROM System IMPORT TermProcedure;
  CONST SetEnvironment  = 1;
        GetEnvironment  = 3;
  TYPE  Environment = BITSET;
  VAR environ : Environment; ok : BOOLEAN;
  PROCEDURE SANE(VAR e: Environment; OpWord: CARDINAL); CODE 0A9EBH;
  PROCEDURE SaveFPEnv;
  BEGIN
    SANE(environ, GetEnvironment)
  END SaveFPEnv;
  PROCEDURE ClearFPEnv;
  VAR e: Environment;
  BEGIN e := {};
    SANE(e, SetEnvironment)
  END ClearFPEnv;
  PROCEDURE RestoreFPEnv;
  VAR e: Environment;
  BEGIN e := environ;
    SANE(e, SetEnvironment)
  END RestoreFPEnv;
BEGIN
  SaveFPEnv; ClearFPEnv;
  TermProcedure(RestoreFPEnv,ok);
  IF ~ok THEN RestoreFPEnv END;
END FPUControl. (* Copyright Departement Informatik, ETH Zuerich, Switzerland, 1992 *)
