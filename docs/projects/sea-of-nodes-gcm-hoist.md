# Checked hoisting across a pure typed diamond

Click's PLDI ’95 §§2.2–2.4 constrains placement by the availability of inputs
and the dominance of uses. A Phi operand is read on its corresponding
incoming occurrence. This profile uses the finite cut picker and the same
typed CFG that the placement checker inspects. The source is a structured
diamond whose typing fixes the producer and its single use.
[PLDI ’95 paper][paper] · [Archived PDF][pdf] · [Cut discovery][discovery]

## Cut and rewrite

Entry binds a seed operand, then branches on a typed input selector. The
true edge passes the seed and an independent payload. The true arm runs a
unary producer and forwards its result and payload to the join. The false
arm forwards its fallback and its own payload. The join returns both
arguments. The seed and producer can have different operand and result
widths.

The producer's input comes from the entry seed via the true block argument.
Its definition is available at entry cut one, after the seed. Its only use
is argument zero on the true arm's jump to the join, a `Use.phi` in the
actual source CFG. `pickAndHoist?` calls `discoverPlacement` on these sites
and supplies that cut to `hoistAt?`. The rewrite supports entry cut one
when `checkPlacement` accepts it. Entry cut zero precedes the seed and
fails operand availability. [Definitions][defs] · [Placement checker][checker]

The rewrite keeps the seed and the branch condition, inserts the producer
after the seed, and removes its binding from the true arm. It appends the
producer result to the true edge's typed arguments and redirects the
true arm's join operand to that parameter. Both original true-edge arguments
retain their values and positions. The false edge and both ordered
incoming join argument pairs keep their values. [Definitions][defs]

## Observation and boundary

`entry_eval_routes` certifies the selector and original entry argument
values. `throughArm_eq_join` certifies the selected join edge and its
ordered arguments. `run_observation` gives the result of the actual CF
interpreter at every fuel budget. `pickAndHoist?_correct` ties the chosen
legal cut to the typed output and proves execution equality.
`pickAndHoist?_returns_iff` preserves and reflects finite returns.
[Theorem header][thms]

The proof quantifies over `Pure.Eval`, whose interpretations are total
functions of the typed operands. The producer now executes even when
the false branch is taken. Effects, faults, and instruction counts are
outside this observation model. The admitted fragment has one seed, one
unary producer, and an acyclic diamond. The pass expects a typed diamond
description and a sound dominator certificate. Matching arbitrary CFGs
and moving code in loops are outside this slice.

The regression discovers entry cut one, moves the binding from the true
arm to entry, and checks the actual typed argument vectors. Both CFGs
return `(36, 41)` on the true branch and `(93, 57)` on the false branch.
Cut zero passes the control and use checks with an empty operand list,
then fails with the actual seed site, and the rewrite rejects it.
[Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.Hoist.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.Hoist.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.Hoist.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.Regression
```

[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/Hoist/Defs.lean
[thms]: ../../Silmaril/SSA/SeaOfNodes/GCM/Hoist/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/Hoist/Regression.lean
[checker]: sea-of-nodes-gcm-legality.md
[discovery]: sea-of-nodes-gcm-discovery.md
[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
