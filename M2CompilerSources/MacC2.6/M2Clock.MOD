IMPLEMENTATION MODULE M2Clock;  (* W. Heiz, 23-Dec-85 / 23-Dec-85 *)
  FROM SYSTEM IMPORT ADDRESS, ADR, LONG, SETREG, REG, INLINE, VAL;
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
  BEGIN
    SETREG(0, seconds); SETREG(8, ADR(dateAndTime)); INLINE(0A9C6H);
  END Secs2Date;
  PROCEDURE SetTime(t: Time); END SetTime;
  PROCEDURE GetTime(VAR t: Time);
    VAR p: POINTER TO LONGINT; dt: DateTimeRec;
  BEGIN
    p := VAL(ADDRESS, LONG(20CH)); Secs2Date(p^, dt);
    WITH dt DO
      t.day         := VAL(CARDINAL, ((year-1900)*20B + month)*40B + day);
      t.minute      := VAL(CARDINAL, hour*60 + minute);
      t.millisecond := VAL(CARDINAL, second*1000);
    END;
  END GetTime;
END M2Clock. (* Copyright Departement Informatik, ETH Zuerich, Switzerland, 1992 *)
