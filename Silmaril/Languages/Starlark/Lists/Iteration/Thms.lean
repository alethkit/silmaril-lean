module

public import Silmaril.Languages.Starlark.Lists.Iteration.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.Iteration.Eval
import Silmaril.Proofs.Languages.Starlark.Lists.Iteration.Cleanup
import Silmaril.Proofs.Languages.Starlark.Lists.Iteration.Truth

public section

namespace Silmaril.Languages.Starlark.Lists.Iteration

theorem projectCell_finishState {α : Type} (address : Address) (project : Contents → Option α)
    (state : State) : finishState (projectCell address project state) = state :=
  Proofs.Languages.Starlark.Lists.Iteration.projectCell_finishState address project state

theorem map_finishState {α β : Type} (action : Meaning α) (f : α → β) (state : State) :
    finishState ((f <$> action) state) = finishState (action state) :=
  Proofs.Languages.Starlark.Lists.Iteration.map_finishState action f state

/-- Truth testing reads the store and preserves it on success and failure. -/
theorem truth_finishState (value : Value) (state : State) :
    finishState (truth value state) = state :=
  Proofs.Languages.Starlark.Lists.Iteration.truth_finishState value state

/-- The suite denotation agrees with the independent rules on exact outcomes. -/
theorem runs_iff_denoteSuite {depth : Nat} (code : Suite depth) (state : State)
    (out : Outcome Flow) : Runs state (.suite code) out ↔ denoteSuite code state = out :=
  ⟨Proofs.Languages.Starlark.Lists.Iteration.denoteSuite_eq_of_runs,
    fun h => h ▸ Proofs.Languages.Starlark.Lists.Iteration.runs_denoteSuite code state⟩

/-- Every suite exit restores the incoming active iterators, including dynamic errors. -/
theorem iterators_denoteSuite {depth : Nat} (code : Suite depth) (state : State) :
    (finishState (denoteSuite code state)).iterators = state.iterators :=
  Proofs.Languages.Starlark.Lists.Iteration.iterators_denoteSuite code state

/-- A loop keeps the iterator stack left by its operand, including on abrupt exits. -/
theorem iterators_denoteForIn (target : Binding) (body : Meaning Flow) (operand : Outcome Value) :
    (finishState (denoteForIn target body operand)).iterators = (finishState operand).iterators :=
  Proofs.Languages.Starlark.Lists.Iteration.iterators_denoteForIn target body operand

/-- The mutable-cell guard rejects edits through any alias of an actively iterated cell. -/
theorem editCell_iterating (state : State) (address : Address)
    (edit : Contents → Except Error Contents) {cell : Cell}
    (found : state.heap[address]? = some cell) (mutable : cell.frozen = false)
    (active : address ∈ state.iterators) :
    editCell address edit state = .error (.activeIteration address) state :=
  Proofs.Languages.Starlark.Lists.Iteration.editCell_iterating state address edit found mutable active

end Silmaril.Languages.Starlark.Lists.Iteration
