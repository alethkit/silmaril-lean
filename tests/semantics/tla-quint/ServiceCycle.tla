----------------------------- MODULE ServiceCycle -----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache, Variants

VARIABLE
  (*
    @type: Int;
  *)
  phase

(*
  @type: (() => Bool);
*)
init == phase = 0

(*
  @type: (() => Bool);
*)
service == phase = 1 /\ phase' := 3

(*
  @type: (() => Bool);
*)
atStart == phase = 0

(*
  @type: (() => Bool);
*)
step ==
  (phase = 0 /\ phase' := 1)
    \/ (phase = 1 /\ phase' := 2)
    \/ ((phase = 2 \/ phase = 3) /\ phase' := 1)
    \/ service

(*
  @type: (() => Bool);
*)
q_init == init

(*
  @type: (() => Bool);
*)
safe == atStart /\ []([step]_phase)

(*
  @type: (() => Bool);
*)
q_step == step

(*
  @type: (() => Bool);
*)
weak == safe /\ WF_phase(service)

(*
  @type: (() => Bool);
*)
strong == safe /\ SF_phase(service)

================================================================================
