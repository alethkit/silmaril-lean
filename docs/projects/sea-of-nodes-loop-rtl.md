# A tail-tested Sea of Nodes word loop in machine RTL

`Silmaril.Machine.SeaOfNodes.Loop.RTL.graph` is a native
`Loop.Graph` with two 64-bit word inputs, one carried word and a fixed pure
producer table. Start latches `seed`. An activation computes `old - delta`
with wrapping subtraction. A nonzero result feeds back into Phi, while
a zero result exits with the old carried word. The source runs with its
own `Graph.ReturnsAfter` relation, which counts completed backedges.
[Native loop][source] · [Loop Region and Phi (§§2.3, 3.1–3.2)][paper]

`lower` emits one machine `RTL.SSA` function. The preheader at label 0
passes the seed to label 1. The header runs the shared word emitter from
the [word diamond][diamond]. Its nonzero arm passes the subtraction result
back to its parameter, and its zero arm passes the old value to the exit
at label 2. `incoming_operand` checks the preheader occurrence `(0, 0)`
and feedback occurrence `(1, 0)` against the emitted terminators. Each pair
is a source block label and a zero-based successor ordinal.
`step_entry` and `step_feedback` describe the actual machine steps, including
the exact updated frame and unchanged stack and memory.
[Emission][defs] · [Machine evaluator][machine]

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Thms`. Use `lower_wellFormed`
for the function's SSA check and `(lower_returns_iff seed delta initial final returned).mp`
to recover the native finite return, singleton result and equality of
the entire memory from `lower.oracle 0 [seed, delta] initial returned final`.
Use `.mpr` for the reverse direction. The proof covers all seeds and
strides for this fixed graph. It makes no termination claim and assumes
no effects, calls, traps or nested control. The regression runs the
actual machine through an immediate exit and a two-backedge run that
latches 3, 2 and 1. The runs return different words over the same nonempty
memory. [Theorem header][thms] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Diamond.RTL.Regression
lake env leanchecker Silmaril.Machine.SeaOfNodes.Loop.RTL.Thms
lake env leanchecker Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Correctness
```

[source]: ../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean
[paper]: https://doi.org/10.1145/202530.202534
[diamond]: sea-of-nodes-diamond-rtl.md
[defs]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Defs.lean
[machine]: ../../Silmaril/Raw/Machine/RTL/SSA.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Thms.lean
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Regression.lean
