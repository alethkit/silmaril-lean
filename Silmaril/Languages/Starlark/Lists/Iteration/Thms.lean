module

public import Silmaril.Languages.Starlark.Lists.Iteration.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.Iteration.Eval
import Silmaril.Proofs.Languages.Starlark.Lists.Iteration.Cleanup

public section

namespace Silmaril.Languages.Starlark.Lists.Iteration

/-- The suite denotation agrees with the independent rules on exact outcomes. -/
theorem runs_iff_denoteSuite {depth : Nat} (code : Suite depth) (state : State)
    (out : Outcome Flow) : Runs state (.suite code) out ↔ denoteSuite code state = out :=
  ⟨Proofs.Languages.Starlark.Lists.Iteration.denoteSuite_eq_of_runs,
    fun h => h ▸ Proofs.Languages.Starlark.Lists.Iteration.runs_denoteSuite code state⟩

/-- Every suite exit restores the incoming active iterators, including dynamic errors. -/
theorem iterators_denoteSuite {depth : Nat} (code : Suite depth) (state : State) :
    (finishState (denoteSuite code state)).iterators = state.iterators :=
  Proofs.Languages.Starlark.Lists.Iteration.iterators_denoteSuite code state

/-- An edit through any alias of an actively iterated mutable list fails after validation. -/
theorem updateCell_iterating (state : State) (address : Address)
    (edit : List Value → Except Error (List Value)) {cell : Cell}
    (found : state.heap[address]? = some cell) (mutable : cell.frozen = false)
    (active : address ∈ state.iterators) :
    updateCell address edit state =
      match edit cell.elements with
      | .ok _ => .error (.activeIteration address) state
      | .error error => .error error state :=
  Proofs.Languages.Starlark.Lists.Iteration.updateCell_iterating state address edit found mutable active

end Silmaril.Languages.Starlark.Lists.Iteration
