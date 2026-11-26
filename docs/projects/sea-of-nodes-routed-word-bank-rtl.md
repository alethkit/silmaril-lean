# Routed word banks in machine RTL

`Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing` builds a native
`Loop.Graph` from checked argument columns and emits an actual
`RTL.SSA` function. Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms`.
[Native Loop and Phi rules][source] · [Word producer emitter][emitter]

The loop profile has three i64 payload slots and one i64 countdown
slot. Each entry column has three indices into the four function
arguments `[count, first, second, third]`. Each feedback column has
three indices into the eight header arguments. Positions 0–3
are the original inputs and positions 4–7 are the old countdown
and old payloads. Repeated operands are valid. The first block argument
receives the input count at entry and its decrement on feedback.
The header's fixed pure schedule emits the constants, wrapping subtraction,
and the nonzero comparison with the existing `WordOp` emitter.
The exit returns the first payload. [Representation][defs]

`lowerChecked [3, 1, 2] [6, 7, 5]` emits a loop whose entry selects
`[third, first, second]` and whose feedback rotates the old payloads to
`[second, third, first]`. On inputs `[1, 10, 20, 30]`, the machine first
latches `[1, 30, 10, 20]`, then `[0, 10, 20, 30]`, and returns `10`.
The last feedback operand reads the old first payload even though the
first destination is also written by the transfer. The executable
check rejects invalid source indices and column lengths and runs the
existing machine SSA checker on the resulting function. [Regression][regression]

`checkRoutes_registers` proves that the decoded indices become the
actual operand registers in order. `step_entry` and `step_feedback`
specify both incoming terminators from a single predecessor frame.
`header_agrees` relates one native activation to the exact RTL
successor after the producer instructions and selected branch.
`lower_returns_iff` relates both finite-return semantics, preserving the
singleton word and entire memory. Both theorems apply to all typed routes
in the three-payload profile. `lowerChecked_eq_some_iff` exposes the typed
routes and the machine well-formedness proof from a successful check.
[Theorem header][thms] · [Machine transfer][machine]

The lower-level `emitColumn`, `readColumn_eq` and `transfer_column`
support arbitrary all-word column arity, given matching native and
machine reads. The executable loop profile uses a fixed schedule and
allows payload routes from its predecessor arguments.

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Regression
lake env leanchecker Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Column
lake env leanchecker Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Execution
```

[source]: ../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean
[emitter]: ../../Silmaril/Machine/SeaOfNodes/Diamond/RTL/Defs.lean
[defs]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Defs.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Thms.lean
[machine]: ../../Silmaril/Raw/Machine/RTL/SSA.lean
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Regression.lean
