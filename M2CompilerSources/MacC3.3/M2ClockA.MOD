IMPLEMENTATION MODULE M2ClockA;  (* WH 23.12.85; HS 21.3.91 *)
  FROM SYSTEM IMPORT ADDRESS, ADR, SETREG, INLINE, VAL;
  TYPE
    DateTimeRec = RECORD
                    year:      INTEGER;
                    month:     INTEGER;
                    day:       INTEGER;
                    hour:      INTEGER;
                    minute:    INTEGER;
                    second:    INTEGER;
                    dayOfWeek: INTEGER;
                  END;
  PROCEDURE Secs2Date(seconds: LONGINT; VAR dateAndTime: DateTimeRec);
  CONST D0 = 0; A0 = 8;
  BEGIN
    SETREG(D0, seconds); SETREG(A0, ADR(dateAndTime)); INLINE(0A9C6H);
  END Secs2Date;
  PROCEDURE SetTime(t: Time); END SetTime;
  PROCEDURE GetTime(VAR t: Time);
    VAR p: POINTER TO LONGINT; dt: DateTimeRec;
  BEGIN
    p := VAL(ADDRESS, 020CH);
    Secs2Date(p^, dt);
    WITH dt DO
      t.day         := ((year-1900)*20B + month)*40B + day;
      t.minute      := hour*60 + minute;
      t.millisecond := second*1000;
    END;
  END GetTime;
END M2ClockA. (* Copyright Departement Informatik, ETH Zuerich, Switzerland, 1992 *)
