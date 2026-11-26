---- MODULE ServiceReplay ----
EXTENDS ServiceCycle

ReplayInit == phase = 0
ReplayNext(target) ==
  IF phase = 1 THEN phase' = target ELSE phase' = 1
GoodNext == ReplayNext(3)
BadNext == ReplayNext(2)
Good == ReplayInit /\ [][GoodNext]_phase /\ WF_phase(GoodNext)
Bad == ReplayInit /\ [][BadNext]_phase /\ WF_phase(BadNext)
====
