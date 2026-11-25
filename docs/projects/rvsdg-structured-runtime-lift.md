# Lifting the ordered RVSDG runtime model

A lawful monad lift preserves `pure` and bind. The RVSDG model lifts each
effectful primitive and keeps its value/control data and pure functions.
`eval_lift` proves that this commutes with every checked term fold, with
the same numbered pure scope and runtime discipline. In the γ case it
lifts the selected arm and then its continuation. `denoteGraph_lift`
expresses the same property for a checked numbered graph.
[Definitions](../../Silmaril/SSA/RVSDG/OrderedRuntime/Structured/Theta/Lift/Defs.lean) ·
[Theorems](../../Silmaril/SSA/RVSDG/OrderedRuntime/Structured/Theta/Lift/Thms.lean)

For total state actions, the lift into `StateT σ Part` embeds the returned
value together with the new state. `Theta.step_liftTotal` proves that
lifting each primitive before evaluating the body gives the same tagged
state action as lifting the already interpreted total body. The equal
actions can then be closed by the same Kleisli Elgot iteration.
`Theta.observe_liftTotal` identifies the decoded final observation with
the one covered by the finite-return and divergence theorems of the
[ordered θ interpretation](rvsdg-structured-runtime-theta.md).

The term and graph theorem requires only preservation of pure actions
and sequencing. The θ comparison lifts the body before iteration. It
uses no commutation law for effects and no iteration on `StateM`. It
covers the one-runtime checked fragment with total bodies. Source pins
for the syntax and the Elgot iteration are in the
[ordered θ project note](rvsdg-structured-runtime-theta.md#sources).

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Lift.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Lift.Thms
lake env leanchecker Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Lift.Thms
```
