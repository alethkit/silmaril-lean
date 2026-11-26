module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defs
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.State

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration

/-- A mutation can edit collections. Saved closures and lexical cells
below the current activation still hold their previous contents. -/
@[expose] def Protected : Contents → Prop
  | .binding _ | .function _ => True
  | _ => False

/-- State transition needed between commands that leave all tracked
bindings in place before committing their result to the destination. -/
structure Preserves (before after : State) : Prop where
  slots : after.slots = before.slots
  cells : ∀ (address : Nat) (cell : Cell), before.heap[address]? = some cell → Protected cell.contents →
    after.heap[address]? = some cell

theorem Preserves.refl (state : State) : Preserves state state :=
  ⟨rfl, fun _ _ cell _ => cell⟩

theorem Preserves.push (state : State) (added : Cell) : Preserves state { state with heap := state.heap.push added } := by
  refine ⟨rfl, ?_⟩
  intro address cell stored _
  have within := (Array.getElem?_eq_some_iff.mp stored).choose
  simp [Array.getElem?_push, Nat.ne_of_lt within, stored]

theorem Preserves.of_old_cells {state next : State} (slots : next.slots = state.slots)
    (old : ∀ address, address < state.heap.size → next.heap[address]? = state.heap[address]?) :
    Preserves state next :=
  ⟨slots, fun address _ stored _ => (old address (Array.getElem?_eq_some_iff.mp stored).choose).trans stored⟩

theorem Preserves.layout {globals : List String} {state next : State} (preserves : Preserves state next)
    (layout : ModuleSlots globals state) : ModuleSlots globals next := by
  refine ⟨by simpa only [RootCall.DistinctOwned, preserves.slots] using layout.distinct, ?_⟩
  intro name present
  obtain ⟨address, value, frozen, own, cell⟩ := layout.usable name present
  exact ⟨address, value, frozen, preserves.slots ▸ own, preserves.cells _ _ cell trivial⟩

theorem Preserves.live {globals : List String} {state next : State} (preserves : Preserves state next)
    {name : String} {address id : Nat} {captures : List Capture} {frozen : Bool}
    (layout : ModuleSlots globals state) (member : name ∈ globals)
    (live : RootCall.Live state name address id captures frozen) :
    RootCall.Live next name address id captures frozen := by
  obtain ⟨slot, _, _, owned, cell⟩ := layout.usable name member
  exact ⟨⟨slot, preserves.slots ▸ owned⟩,
    (retain_read owned preserves.slots ((preserves.cells _ _ cell trivial).trans cell.symm)).trans live.binding,
    preserves.cells _ _ live.cell trivial⟩

private theorem edit_keeps {before after : State} {address : Nat} {edit : Contents → Except Error Contents}
    (ran : editCell address edit before = .ok () after) :
    ∀ (key : Nat) (cell : Cell), before.heap[key]? = some cell → Protected cell.contents → after.heap[key]? = some cell := by
  intro key cell stored keepCell
  unfold editCell getCell at ran
  simp only [bind, EStateM.bind] at ran
  cases current : before.heap[address]? with
  | none => simp [current] at ran
  | some old =>
    simp only [current] at ran
    split at ran <;> try contradiction
    split at ran <;> try contradiction
    split at ran <;> try contradiction
    split at ran <;> try contradiction
    rename_i replacement valid
    cases ran
    have outside : address ≠ key := by
      intro equal
      subst key
      rw [current] at stored
      cases stored
      rcases cell with ⟨contents, frozen⟩
      cases contents <;> simp_all [Protected, Contents.sameMutableKind]
    simp [outside, stored]

private theorem checked_write_keeps {before after : State} {receiver index value : Value}
    (ran : writeIndex receiver index value before = .ok () after) :
    ∀ (address : Nat) (cell : Cell), before.heap[address]? = some cell → Protected cell.contents → after.heap[address]? = some cell := by
  cases receiver with
  | list address =>
    unfold writeIndex updateCell at ran
    simp only [bind, EStateM.bind] at ran
    have fixed : finishState (listElements address before) = before :=
      projectCell_finishState _ _ _
    cases elements : listElements address before with
    | error error final => simp [elements] at ran
    | ok items final =>
      rw [elements] at fixed
      change final = before at fixed
      subst final
      simp only [elements] at ran
      cases normalized : normalizeIndex items.length index with
      | error error =>
        simp only [normalized, fromExcept, Except.bind] at ran
        change EStateM.Result.error error before = _ at ran
        cases ran
      | ok offset =>
        simp only [normalized, Except.bind] at ran
        change editCell address (fun _ => .ok (.list (items.set offset.val value))) before = _ at ran
        exact edit_keeps ran
  | dict address =>
    rw [writeIndex, writeDict] at ran
    exact edit_keeps ran
  | scalar | tuple | function | builtin | string | range => cases ran

theorem leaf_preserves (caller : State) (frame : Forwarding.Frame) (captures : List Capture)
    (assigned : List (Binding × Value)) (plan : Leaf.Plan) {out : Outcome Flow}
    (source : Leaf.Runs plan (activate caller frame.declaration captures assigned) out) :
    ∀ value after, Leaf.returnTo caller out = .ok value after → Preserves caller after := by
  intro value after returned
  cases source with
  | rhsError _ | unpackError _ _ => cases returned
  | @leaves rhs first second read unpacked =>
    let named := (activate caller frame.declaration captures assigned).write plan.destination first
    have stable (key : Nat) (cell : Cell) (stored : caller.heap[key]? = some cell) :
        named.heap[key]? = some cell :=
      (Wrapper.activated_write_preserves caller frame captures assigned plan.destination first key
        (Array.getElem?_eq_some_iff.mp stored).choose).trans stored
    change Leaf.returnTo caller ((Leaf.store plan second named).resume _) = _ at returned
    unfold Leaf.store at returned
    cases recv : named.bindingValue plan.receiver with
    | error error => simp [State.read, recv, Outcome.resume, Leaf.returnTo] at returned
    | ok receiver =>
      cases sub : named.bindingValue plan.index with
      | error error => simp [State.read, recv, sub, Outcome.resume, Leaf.returnTo] at returned
      | ok index =>
        cases written : writeIndex receiver index second named with
        | error error final => simp [State.read, recv, sub, written, Outcome.resume, Leaf.returnTo] at returned
        | ok result final =>
          cases result
          cases read : final.bindingValue plan.returned with
          | error error => simp [State.read, recv, sub, written, read, Outcome.resume, Leaf.returnTo] at returned
          | ok result =>
            simp [State.read, recv, sub, written, read, Outcome.resume, Leaf.returnTo, pure, EStateM.pure] at returned
            rcases returned with ⟨_, rfl⟩
            exact ⟨rfl, fun key cell stored kind => checked_write_keeps written key cell (stable key cell stored) kind⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings
