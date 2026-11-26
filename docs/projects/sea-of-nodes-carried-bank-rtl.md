# The counted-swap bank in machine RTL

`Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank` lowers the existing
native counted-swap `Loop.Graph`. The bank carries two 64-bit payload
words and a separate 64-bit loop index. The concrete pure model starts
the index at zero and tests it against the unsigned limit. A taken
backedge increments the index and exchanges the payloads. The exit
returns the wrapping difference of the two payloads in their current
order. [Native counted-swap graph][source] · [Loop Region and Phi][paper]

`lowerChecked` checks the typed producer opcodes and wire addresses,
including the full entry and feedback columns, guard, and return.
`lowerChecked_eq_some_iff` characterizes successful admission by exact
equality with the native graph. The emitted preheader supplies the
index seed and the literal increment. The header has three actual
RTL.SSA instructions and a conditional terminator. Its backedge passes
`[second, first, nextIndex]` to the header's `[first, second, index]`.
`step_entry` and `step_feedback` specify those steps from one old
register file and preserve the stack and memory. `incoming_operand`
checks the entry at source occurrence `(0, 0)` and feedback at `(1, 0)`.
[Emission][defs] · [Machine transfer][machine]

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Thms`.
Given `ok : lowerChecked graph = some target`, `checked_wellFormed ok`
checks the actual machine program. `lower_returns_iff ok` relates native
finite return to the machine oracle with singleton result and the entire
memory unchanged. `lower_stepsN_iff ok` relates `n` native backedges to
exactly `4 * n + 7` running steps and a terminal return. The count is three
preheader steps and four per activation, including the exit activation.
[Theorem header][thms]

The regression checks zero, one and two backedges on nonempty memory.
The odd case reads both crossed words in the actual frame and would
return a different word if a sequential copy duplicated a payload.
The matcher rejects that same-typed wiring.
[Regression][regression]

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Regression
lake env leanchecker Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Correctness
lake env leanchecker Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Thms
```

[source]: ../../Silmaril/SSA/SeaOfNodes/Loop/LambdaSSA/Defs.lean
[paper]: https://doi.org/10.1145/202530.202534
[defs]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/CarriedBank/Defs.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/CarriedBank/Thms.lean
[machine]: ../../Silmaril/Raw/Machine/RTL/SSA.lean
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/CarriedBank/Regression.lean
