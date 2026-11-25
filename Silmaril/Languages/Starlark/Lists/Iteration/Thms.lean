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

/-- Exact agreement between cursor yield rules and materialization. -/
theorem cursorCollects_iff_collect (cursor : Cursor) (values : List Value) :
    CursorCollects cursor values ↔ cursor.collect = values :=
  Proofs.Languages.Starlark.Lists.Iteration.cursorCollects_iff_collect cursor values

/-- The remaining count is the number of yielded values. -/
theorem cursorCollects_length {cursor : Cursor} {values : List Value}
    (ran : CursorCollects cursor values) : values.length = cursor.remaining :=
  Proofs.Languages.Starlark.Lists.Iteration.cursorCollects_length ran

/-- A successful node unpack supplies exactly one value per child. -/
theorem unpacksValue_length {s t : State} {value : Value} {arity : Nat} {values : List Value}
    (ran : UnpacksValue s value arity (.ok values t)) : values.length = arity := by
  cases ran with
  | items _ size yields => exact (cursorCollects_length yields).trans size

/-- The target rules determine the exact writes or error and final state. -/
theorem bindsTarget_iff_bindTarget (state : State) (value : Value) (target : LoopTarget)
    (out : Outcome Unit) : BindsTarget state value target out ↔ bindTarget target value state = out :=
  ⟨Proofs.Languages.Starlark.Lists.Iteration.bindTarget_eq_of_binds,
    fun same => same ▸ Proofs.Languages.Starlark.Lists.Iteration.bindsTarget_bindTarget state value target⟩

/-- An error checking a node's item preserves that node's incoming state. -/
theorem unpackValue_failure_state {s final : State} {value : Value} {arity : Nat}
    {error : Error} (ran : UnpacksValue s value arity (.error error final)) : final = s :=
  Proofs.Languages.Starlark.Lists.Iteration.unpackValue_failure_state ran

/-- A flat pattern still preserves its complete incoming state on failure. -/
theorem bindsTarget_failure_state {s final : State} {value : Value} {bindings : List Binding}
    {error : Error} (ran : BindsTarget s value (.unpack bindings) (.error error final)) : final = s :=
  Proofs.Languages.Starlark.Lists.Iteration.bindsTarget_failure_state ran

/-- Cursor stepping agrees with iteration denotation when body outcomes agree. -/
theorem cursor_eq_of_runs {body : State → Outcome Flow → Prop} {meaning : Meaning Flow}
    {target : LoopTarget} {cursor : Cursor} {state : State} {out : Outcome Flow}
    (bodyEq : ∀ s result, body s result → meaning s = result)
    (ran : CursorRuns body target cursor state out) :
    denoteCursor target meaning cursor state = out :=
  Proofs.Languages.Starlark.Lists.Iteration.cursor_eq_of_runs bodyEq ran

/-- Cursor iteration has a derivation given a derivation for each body outcome. -/
theorem cursor_runs_denote (body : State → Outcome Flow → Prop) (meaning : Meaning Flow)
    (bodyRuns : ∀ s, body s (meaning s)) (target : LoopTarget) (cursor : Cursor) (state : State) :
    CursorRuns body target cursor state (denoteCursor target meaning cursor state) :=
  Proofs.Languages.Starlark.Lists.Iteration.cursor_runs_denote body meaning bodyRuns target cursor state

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
theorem iterators_denoteForIn (target : LoopTarget) (body : Meaning Flow) (operand : Outcome Value) :
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
