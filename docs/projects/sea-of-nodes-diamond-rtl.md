# A Sea of Nodes word diamond in machine RTL

The bridge emits one machine RTL.SSA function directly from the source-native
single-diamond graph. Its profile has two 64-bit word inputs, one Boolean branch
predicate, and one word-valued Phi returned at the Region. The typed
`WordOp` signature admits word constants, wrapping add and subtract, and word
equality. The source evaluates equality to a Boolean. The target comparison
encodes it as word 0 or 1, which the RTL conditional tests for nonzero.
[Source graph][source] · [Bridge definitions][defs]

| Block | Operations and terminator |
| --- | --- |
| 0 | Bind the two entry words, emit each pure producer once in source order, and branch to 1 on nonzero or 2 on zero. |
| 1 | Jump to 3 with the operand at the Region slot for the true projection. |
| 2 | Jump to 3 with the operand at the Region slot for the false projection. |
| 3 | Bind the incoming word to the single block parameter and return it. |

The two predecessor blocks carry their own register arguments even though they
have the same destination. The source Region may store its predecessors in
either order. The lowering resolves the slot from the projection before
emitting the argument. RTL transfer reads that argument from the predecessor's
frame and writes the join parameter. The fixture checks distinct incoming
operand registers, both branch results under both Region orders, and word wraparound.
[RTL machine][machine] · [Regression][regression]

`lower_returns_iff` compares the independent source `Graph.Returns` relation
with the existing RTL `Prog.oracle`, which runs from a fresh frame and observes
the whole-program return. Every admitted source input returns one word in RTL
with identical memory, and every RTL return has that source result and memory.
The proof relates the source's typed producer store to RTL registers, then
uses the existing bridge between RTL's block execution and machine steps.
`lower_forward` shows that every emitted edge goes to a strictly greater
block label. Loops, backedges, calls, effects, partial operators, and general
Sea of Nodes scheduling are outside the profile. [Theorem header][thms]

The scoped build and kernel replay can be run with the pinned toolchain.

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Diamond.RTL.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Diamond.RTL.Regression
lake env leanchecker Silmaril.Proofs.Machine.SeaOfNodes.Diamond.RTL.Correctness
lake env leanchecker Silmaril.Machine.SeaOfNodes.Diamond.RTL.Thms
```

[source]: ../../Silmaril/SSA/SeaOfNodes/Diamond/Defs.lean
[defs]: ../../Silmaril/Machine/SeaOfNodes/Diamond/RTL/Defs.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Diamond/RTL/Thms.lean
[machine]: ../../Silmaril/Raw/Machine/RTL/SSA.lean
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Diamond/RTL/Regression.lean
