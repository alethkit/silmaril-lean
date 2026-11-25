---- MODULE ReferenceForms ----
EXTENDS Naturals
VARIABLE x

---- MODULE Child ----
THEOREM Claim == TRUE
<1>outer. TRUE
  <3>inner. TRUE OBVIOUS
  <3> QED BY <3>inner
<1> QED BY <1>outer
====

ChildInstance == INSTANCE Child
Step == x' = x + 1
Spec ==
  /\ [][Step]_x
  /\ \/ WF_x(Step)
     \/ SF_<<x, x>>(Step)
Arithmetic == 1 + Term:: 2 * 3
====
