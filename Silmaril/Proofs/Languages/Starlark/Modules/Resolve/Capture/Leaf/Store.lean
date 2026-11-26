module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration (unpackValue acquireIterator iterationSource)

@[expose] def withFrame (state frame : State) : State :=
  { state with bindings := frame.bindings, slots := frame.slots }

@[expose] def mapState {α : Type} (f : State → State) (out : Outcome α) : Outcome α :=
  match out with
  | .ok value state => .ok value (f state)
  | .error error state => .error error (f state)

private def Insensitive {α : Type} (action : Meaning α) : Prop :=
  ∀ state bindings, action (withFrame state bindings) =
    mapState (fun final => withFrame final bindings) (action state)

private theorem insensitive_bind {α β : Type} {first : Meaning α} {rest : α → Meaning β}
    (lhs : Insensitive first) (rhs : ∀ value, Insensitive (rest value)) : Insensitive (first >>= rest) := by
  intro state bindings
  have step := lhs state bindings
  cases ran : first state with
  | ok value next =>
    rw [ran] at step
    simpa [bind, EStateM.bind, step, ran, mapState] using rhs value next bindings
  | error error next =>
    rw [ran] at step
    simp [bind, EStateM.bind, step, ran, mapState]

private theorem insensitive_pure {α : Type} (value : α) : Insensitive (pure value) := by intro state frame; rfl

private theorem insensitive_throw {α : Type} (error : Error) : Insensitive (throw (m := Meaning) (α := α) error) := by
  intro state frame; rfl

private theorem insensitive_from_except {α : Type} (value : Except Error α) : Insensitive (fromExcept value) := by
  cases value <;> intro state frame <;> rfl

private theorem insensitive_get (address : Address) : Insensitive (getCell address) := by
  intro state bindings
  simp only [getCell, withFrame]
  split <;> rfl

private theorem insensitive_project {α : Type} (address : Address) (project : Contents → Option α) :
    Insensitive (projectCell address project) := by
  apply insensitive_bind (insensitive_get address)
  intro cell
  cases project cell.contents
  · exact insensitive_throw _
  · exact insensitive_pure _

private theorem insensitive_map {α β : Type} (f : α → β) {action : Meaning α} (proof : Insensitive action) :
    Insensitive (f <$> action) := by
  change Insensitive (action >>= fun value => pure (f value))
  exact insensitive_bind proof (fun _ => insensitive_pure _)

private theorem insensitive_iteration (value : Value) : Insensitive (iterationSource value) := by
  cases value <;> first | exact insensitive_throw _ | exact insensitive_map _ (insensitive_project _ _)

private theorem insensitive_acquire (value : Value) : Insensitive (acquireIterator value) := by
  cases value <;> first | exact insensitive_pure _ | exact insensitive_map _ (insensitive_iteration _)

theorem unpack_with_frame (arity : Nat) (value : Value) (state : State) (bindings : State) :
    unpackValue arity value (withFrame state bindings) =
      mapState (fun final => withFrame final bindings) (unpackValue arity value state) := by
  unfold unpackValue
  rw [insensitive_acquire value state bindings]
  cases acquireIterator value state with
  | error error next => rfl
  | ok acquired next => by_cases valid : acquired.2.remaining = arity <;> simp [mapState, valid]

private theorem insensitive_edit (address : Address) (edit : Contents → Except Error Contents) :
    Insensitive (editCell address edit) := by
  apply insensitive_bind (insensitive_get address)
  intro cell state bindings
  by_cases frozen : cell.frozen = true
  · simp [withFrame, mapState, frozen]
  · by_cases iterating : address ∈ state.iterators
    · simp [withFrame, mapState, frozen, iterating]
    · cases edited : edit cell.contents with
      | error error => simp [withFrame, mapState, frozen, iterating]
      | ok contents =>
        by_cases kind : cell.contents.sameMutableKind contents = true <;>
          simp [withFrame, mapState, frozen, iterating, kind]

private theorem insensitive_list_write (address : Address) (index value : Value) :
    Insensitive (writeIndex (.list address) index value) := by
  apply insensitive_bind (insensitive_project address _)
  intro elements
  apply insensitive_bind (insensitive_from_except _)
  intro replacement
  exact insensitive_edit _ _

private theorem insensitive_dict_write (address : Address) (key value : Value) :
    Insensitive (writeIndex (.dict address) key value) := by
  intro state bindings
  let edit (state : State) : Contents → Except Error Contents
    | .dict entries => do
      let code ← state.keyOf key
      return .dict (putEntry ⟨key, code, value⟩ entries)
    | _ => .error (.wrongCellKind address)
  change editCell address (edit (withFrame state bindings)) (withFrame state bindings) =
    mapState (fun final => withFrame final bindings) (editCell address (edit state) state)
  have same : (withFrame state bindings).keyOf key = state.keyOf key := by cases key <;> rfl
  have equal : edit (withFrame state bindings) = edit state := by
    funext contents
    cases contents <;> simp [edit, same]
  exact equal ▸ insensitive_edit address (edit state) state bindings

theorem write_with_frame (receiver index value : Value) (state : State) (bindings : State) :
    writeIndex receiver index value (withFrame state bindings) =
      mapState (fun final => withFrame final bindings) (writeIndex receiver index value state) :=
  (show Insensitive (writeIndex receiver index value) from by
    cases receiver with
    | list address => exact insensitive_list_write address _ _
    | dict address => exact insensitive_dict_write address _ _
    | scalar | tuple | function | builtin | string | range => exact insensitive_throw _) state bindings

theorem write_frame {receiver index value : Value} {state : State} {successValue : Unit}
    {error : Error} {next : State}
    (ran : writeIndex receiver index value state = .ok successValue next ∨
      writeIndex receiver index value state = .error error next) :
    next.slots = state.slots ∧ next.bindings = state.bindings := by
  have same := write_with_frame receiver index value state state
  have self : withFrame state state = state := by cases state; rfl
  rw [self] at same
  have frame : next = withFrame next state := by
    rcases ran with ran | ran <;> rw [ran] at same <;> exact (by injection same)
  have slots : next.slots = (withFrame next state).slots := congrArg State.slots frame
  have bindings : next.bindings = (withFrame next state).bindings := congrArg State.bindings frame
  exact ⟨slots, bindings⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf
