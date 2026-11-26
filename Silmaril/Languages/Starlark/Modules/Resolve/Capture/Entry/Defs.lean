module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry

open Lists (State Address)

/-- Positional actuals supply one value to each required parameter. -/
inductive Assigns : List String → List Lists.Value → List (Binding × Lists.Value) → Prop where
  | nil : Assigns [] [] []
  | cons {name : String} {names : List String} {value : Lists.Value} {values : List Lists.Value}
      {assigned : List (Binding × Lists.Value)} :
      Assigns names values assigned → Assigns (name :: names) (value :: values) ((fileSlot name, value) :: assigned)

/-- Binding the evaluated operands of a required positional call either
fills every slot, identifies the missing suffix, or rejects surplus values. -/
inductive Binds : List String → List Lists.Value → Except Lists.Error (List (Binding × Lists.Value)) → Prop where
  | success {names : List String} {values : List Lists.Value} {assigned : List (Binding × Lists.Value)} :
      Assigns names values assigned → Binds names values (.ok assigned)
  | missing {names : List String} {values : List Lists.Value} :
      values.length < names.length → Binds names values (.error (.missingArguments (names.drop values.length)))
  | surplus {names : List String} {values : List Lists.Value} :
      names.length < values.length → Binds names values (.error (.arity names.length values.length))

/-- Every owned slot in the current frame points to a binding cell. The
cell may still be waiting for its first assignment. -/
@[expose] def OwnedCells (state : State) : Prop :=
  ∀ binding address, state.slots binding = some (.owned address) →
    ∃ value frozen, state.heap[address]? = some ⟨.binding value, frozen⟩

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry
