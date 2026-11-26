# Arbitrary-arity routed word banks in machine RTL

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms`.
`BankRoutes n` describes `n` i64 payload words and a separate i64
countdown in slot zero. `BankRoutes.graph` is the native `Loop.Graph`.
It retains the three-payload profile's countdown schedule and uses
the existing `WordOp` emitter. [Native Loop and Phi rules][source] ·
[Definitions][defs] · [Three-payload profile][fixed]

To decode raw routes and check the emitted program, call
`lowerBankChecked n entry feedback result`.

- The entry column has `n` positions into the `n + 1` function inputs,
  with the countdown in position zero.
- The feedback column has `n` positions into the original inputs followed
  by the old bank. Positions `0` through `n` are the inputs. Positions
  `n + 1` through `2 * n + 1` are the old countdown and payloads.
  Repeated operands are valid.
- The return position is zero-based within the payload, represented by
  `Fin n`. Admission rejects zero-payload banks because they have no
  well-typed payload return. The countdown has a fixed entry operand and
  receives its computed decrement on feedback.

Use `lowerBankChecked_eq_some_iff` to recover the typed routes and
the machine SSA well-formedness proof. `checkBankRoutes_registers`
relates the checked indices to the emitted operands and return position.
`bank_step_entry` and `bank_step_feedback` specify the exact machine
transfers. `bank_header_agrees` relates one native activation to the
actual RTL successor. `bank_returns_iff` relates finite returns in both
directions and preserves the whole memory. These proofs are polymorphic
in the payload count and reuse the certified column emitter.
[Theorem header][thms] · [Machine transfer][machine]

The five-payload regression runs
`lowerBankChecked 5 [5, 1, 2, 3, 4] [8, 7, 11, 7, 9] 3`.
On inputs `[1, 10, 20, 30, 40, 50]` the first feedback latches
`[0, 10, 50, 40, 50, 20]` and the selected slot returns `50`.
Both reads of old register 7 see `50` even though that register receives
`10` during transfer. The regression also runs a one-payload bank and
checks rejection of an out-of-range result and a zero-payload bank.
[Regression][regression]

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.ArityRegression
lake env leanchecker Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Frame
lake env leanchecker Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Execution
```

[source]: ../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean
[defs]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Defs.lean
[fixed]: sea-of-nodes-routed-word-bank-rtl.md
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Thms.lean
[machine]: ../../Silmaril/Raw/Machine/RTL/SSA.lean
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/ArityRegression.lean
