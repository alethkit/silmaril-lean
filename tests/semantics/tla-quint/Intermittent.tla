---- MODULE Intermittent ----
VARIABLES ready, done

Init == ready /\ ~done
Next == ready /\ done' = TRUE
vars == <<ready, done>>

Safe == /\ Init
        /\ [][Next]_done
Weak == Safe /\ WF_done(Next)
Strong == Safe /\ SF_done(Next)
Full == Init /\ [][Next]_vars
Both == Full /\ WF_done(Next) /\ SF_<<ready, done>>(Next)
====
