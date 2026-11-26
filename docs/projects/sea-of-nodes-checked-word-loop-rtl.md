# Checked Sea of Nodes word loops in machine RTL

`Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.lower` checks a native
`Loop.Graph` with two 64-bit inputs (seed and stride), one carried word,
an empty preheader, and three header producers. The first producer
wraps `old + stride` or `old - stride`. The second is a word constant.
The third compares the update and the constant using equality or
inequality. True feeds back the update. False returns the old word.
[Native loop][source] · [Checked definitions][defs] · [Original bridge][countdown]

`Checked.recognize_eq_some_iff` characterizes success by equality with
`Profile.graph`. The matcher checks producer operand addresses, separate
entry and feedback operands, the predicate, and the return wire. A valid
typed wire can still be outside the admitted profile.

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Thms`. Given
`ok : Checked.lower graph = some target`, use `Checked.lower_wellFormed ok`
for the machine program check and `Checked.lower_returns_iff ok`
to translate finite returns in either direction, with a singleton word
and the entire memory unchanged. `Checked.lower_stepsN_iff ok` relates
exactly `n` native backedges to `4 * n + 5` running steps followed by
the terminal return step. The count includes the entry jump and the
three instructions and branch of every header activation.
[Theorem header][thms] · [Machine evaluator][machine]

The regression checks the original countdown and a graph with addition,
an equality branch and a nonzero bound. It rejects a constant in the
update position and a same-type limit wired in place of the feedback.
The theorems concern finite runs of pure single loops with this producer
schedule, provenance, and single carried word.
[Regression][regression]

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Checked.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Regression
lake env leanchecker Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Correctness
lake env leanchecker Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Thms
```

[source]: ../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean
[defs]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Checked/Defs.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Checked/Thms.lean
[countdown]: sea-of-nodes-loop-rtl.md
[machine]: ../../Silmaril/Raw/Machine/RTL/SSA.lean
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Checked/Regression.lean
