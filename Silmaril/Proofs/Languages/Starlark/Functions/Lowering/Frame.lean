module

public import Silmaril.Languages.Starlark.Functions.Lowering.Source.Defs
public import Silmaril.Languages.Starlark.Functions.Thms
public import Silmaril.Languages.Starlark.Lists.Thms
import Std.Data.String.ToNat

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Lowering

open Silmaril.Languages.Starlark (Binding Ref LogicalOp)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration (Flow truth)

theorem temporary_inj {i j : Nat} (h : temporary i = temporary j) : i = j := by
  apply Nat.repr_injective
  exact (String.append_right_inj "$expr").mp (by
    simpa only [temporary, Nat.toString_eq_repr] using congrArg Binding.name h)

theorem scratch_mono {i j : Nat} (le : i ≤ j) {name : Binding} :
    Scratch j name → Scratch i name :=
  fun ⟨index, bound, eq⟩ => ⟨index, Nat.le_trans le bound, eq⟩

theorem temporary_protected (i : Nat) : ¬ Scratch (i + 1) (temporary i) := by
  rintro ⟨j, bound, eq⟩
  have := temporary_inj eq
  omega

theorem StateMatch.back {i j : Nat} {s t : State} (h : StateMatch j s t) (le : i ≤ j) :
    StateMatch i s t :=
  ⟨h.heap, h.iterators, h.slots, fun name safe => h.bindings name (safe ∘ scratch_mono le)⟩

theorem StateMatch.free {i : Nat} {s t : State} (h : StateMatch i s t) (free : ScratchFree s) :
    ScratchFree t := fun index => h.slots ▸ free index

theorem StateMatch.write {i : Nat} {s t : State} (h : StateMatch i s t) (name : Binding) (v : Value) :
    StateMatch i (s.write name v) (t.write name v) := by
  cases hs : s.slots name with
  | none =>
    have tslot : t.slots name = none := h.slots ▸ hs
    rw [State.write, State.write, hs, tslot]
    exact ⟨h.heap, h.iterators, h.slots, fun b safe => by by_cases e : b = name <;> simp [e, h.bindings b safe]⟩
  | some slot =>
    have tslot : t.slots name = some slot := h.slots ▸ hs
    rw [State.write, State.write, hs, tslot]
    cases slot with
    | captured => exact h
    | owned address =>
      dsimp only
      have cell : s.heap[address]? = t.heap[address]? := by rw [h.heap]
      rw [cell]
      split
      · exact ⟨by dsimp only; rw [h.heap], h.iterators, h.slots, h.bindings⟩
      · exact h

theorem StateMatch.hideWrite {i : Nat} {s t : State} (h : StateMatch i s t)
    (free : ScratchFree t) {j : Nat} (bound : i ≤ j) (value : Value) :
    StateMatch i s (t.write (temporary j) value) := by
  rw [State.write, free j]
  exact ⟨h.heap, h.iterators, h.slots, fun name safe => by
    have diff : name ≠ temporary j := fun eq => safe ⟨j, bound, eq⟩
    simpa [diff] using h.bindings name safe⟩

theorem read_temp {s : State} (free : ScratchFree s) (i : Nat) {value : Value}
    (saved : s.bindings (temporary i) = some value) :
    denote (.read (.bound (temporary i))) s = .ok value s := by
  simp [denote, State.read, State.bindingValue, free i, saved]

theorem write_temp_read {s : State} (free : ScratchFree s) (i : Nat) (v : Value) :
    (s.write (temporary i) v).bindings (temporary i) = some v := by
  simp [State.write, free i]

@[expose] def rebind (s : State) (bindings : Binding → Option Value) : State :=
  { s with bindings }

theorem same_rebound {i : Nat} {s t : State} (h : StateMatch i s t) :
    rebind s t.bindings = t := by
  cases s; cases t
  have ⟨heap, iterators, slots, _⟩ := h
  unfold rebind
  simp_all

@[expose] def mapFrame {α : Type} (f : State → State) : Outcome α → Outcome α
  | .ok v s => .ok v (f s)
  | .error e s => .error e (f s)

theorem rebind_visible {i : Nat} {s t u : State} (h : StateMatch i s t)
    (same : u.bindings = s.bindings) :
    StateMatch i u (rebind u t.bindings) :=
  ⟨rfl, rfl, rfl, fun name safe => by rw [rebind, same]; exact h.bindings name safe⟩

theorem StateMatch.trans {i : Nat} {s t u : State} (h : StateMatch i s t)
    (k : StateMatch i t u) : StateMatch i s u :=
  ⟨h.heap.trans k.heap, h.iterators.trans k.iterators, h.slots.trans k.slots,
    fun name safe => (h.bindings name safe).trans (k.bindings name safe)⟩

/-- The source effects keep the caller's direct bindings and slot map. -/
@[expose] def SameScope (s t : State) : Prop := s.bindings = t.bindings ∧ s.slots = t.slots

@[expose] def KeepsScope {α : Type} (act : Meaning α) : Prop :=
  ∀ s, SameScope (Iteration.finishState (act s)) s

theorem scopePure {α : Type} (value : α) : KeepsScope (pure value) := fun _ => ⟨rfl, rfl⟩
theorem scopeThrow {α : Type} (e : Error) : KeepsScope (throw e : Meaning α) := fun _ => ⟨rfl, rfl⟩

theorem scopeBind {α β : Type} {act : Meaning α} {next : α → Meaning β}
    (h : KeepsScope act) (k : ∀ value, KeepsScope (next value)) :
    KeepsScope (act >>= next) := by
  intro state
  have kept := h state
  cases he : act state with
  | ok value s =>
    have ⟨bindings, slots⟩ := k value s
    rw [he] at kept
    simpa only [bind, EStateM.bind, he] using
      (show SameScope (Iteration.finishState (next value s)) state from
        ⟨bindings.trans kept.1, slots.trans kept.2⟩)
  | error e s =>
    rw [show (act >>= next) state = .error e s by simp [bind, EStateM.bind, he]]
    rw [he] at kept
    exact kept

/-- An action that neither consults nor writes caller direct bindings. -/
@[expose] def FrameIndependent {α : Type} (act : Meaning α) : Prop :=
  ∀ (s : State) (bindings : Binding → Option Value),
    act (rebind s bindings) = mapFrame (rebind · bindings) (act s)

theorem framePure {α : Type} (x : α) : FrameIndependent (pure x) := fun _ _ => rfl
theorem frameThrow {α : Type} (e : Error) : FrameIndependent (throw e : Meaning α) := fun _ _ => rfl

theorem frameBind {α β : Type} {act : Meaning α} {next : α → Meaning β}
    (h : FrameIndependent act) (k : ∀ value, FrameIndependent (next value)) :
    FrameIndependent (act >>= next) := by
  intro state bindings
  simp only [bind, EStateM.bind, h state bindings]
  cases act state with
  | ok a s => exact k a s bindings
  | error => rfl

theorem frameMap {α β : Type} (f : α → β) {act : Meaning α} (h : FrameIndependent act) :
    FrameIndependent (f <$> act) := by
  intro state bindings
  simp only [Functor.map, EStateM.map, h state bindings]
  cases act state <;> rfl

theorem frameFromExcept {α : Type} (out : Except Error α) :
    FrameIndependent (fromExcept out) := by cases out <;> (intro _ _; rfl)

theorem frameGetCell (address : Address) : FrameIndependent (getCell address) := by
  intro s f
  unfold getCell
  change (match s.heap[address]? with | some cell => _ | none => _) = _
  cases s.heap[address]? <;> rfl

theorem frameProject {α : Type} (address : Address) (project : Contents → Option α) :
    FrameIndependent (projectCell address project) := by
  unfold projectCell
  apply frameBind (frameGetCell address)
  intro cell
  cases project cell.contents
  · exact frameThrow _
  · exact framePure _

theorem frameList (address : Address) : FrameIndependent (listElements address) := frameProject _ _
theorem frameTuple (address : Address) : FrameIndependent (tupleElements address) := frameProject _ _
theorem frameDict (address : Address) : FrameIndependent (dictEntries address) := frameProject _ _

theorem frameTruth (value : Value) : FrameIndependent (truth value) := by
  cases value with
  | list => exact frameMap _ (frameList _)
  | tuple => exact frameMap _ (frameTuple _)
  | dict => exact frameMap _ (frameDict _)
  | _ => exact framePure _

theorem scopeProject {α : Type} (address : Address) (project : Contents → Option α) :
    KeepsScope (projectCell address project) := by
  unfold projectCell
  apply scopeBind
  · intro s
    unfold getCell
    cases s.heap[address]? <;> exact ⟨rfl, rfl⟩
  · intro cell
    cases project cell.contents
    · exact scopeThrow _
    · exact scopePure _

theorem read_match {i : Nat} {s t : State} (h : StateMatch i s t) {name : Binding}
    (safe : ¬ Scratch i name) : t.bindingValue name = s.bindingValue name := by
  simp [State.bindingValue, ← h.heap, ← h.slots, ← h.bindings name safe]

theorem frameRun {α : Type} {act : Meaning α} (h : FrameIndependent act)
    {i : Nat} {s t : State} (same : StateMatch i s t) :
    act t = mapFrame (rebind · t.bindings) (act s) := by
  conv => lhs; rw [← same_rebound same]
  exact h s t.bindings

theorem transportBind {α β : Type} {act : Meaning α} {next : α → Meaning β}
    {s t : State} (h : act t = mapFrame (rebind · t.bindings) (act s))
    (k : ∀ a u, act s = .ok a u →
      next a (rebind u t.bindings) = mapFrame (rebind · t.bindings) (next a u)) :
    (act >>= next) t = mapFrame (rebind · t.bindings) ((act >>= next) s) := by
  simp only [bind, EStateM.bind, h]
  cases he : act s with
  | ok a u => exact k a u he
  | error => rfl

theorem scopeTransport {s t u : State} (same : StateMatch 0 s t)
    (kept : SameScope u s) : StateMatch 0 u (rebind u t.bindings) :=
  rebind_visible same kept.1

theorem reboundMatch (start : Nat) (s : State) (bindings : Binding → Option Value) :
    StateMatch start (rebind s bindings) (rebind s bindings) :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem project_state {α : Type} (address : Address) (project : Contents → Option α)
    (s : State) : Iteration.finishState (projectCell address project s) = s := by
  simp only [projectCell, bind, EStateM.bind, getCell]
  cases hs : s.heap[address]? with
  | none => rfl
  | some cell => dsimp only; cases project cell.contents <;> rfl

theorem map_state {α β : Type} (action : Meaning α) (f : α → β) (s : State) :
    Iteration.finishState ((f <$> action) s) = Iteration.finishState (action s) := by
  simp only [Functor.map, EStateM.map]
  cases action s <;> rfl

end Silmaril.Proofs.Languages.Starlark.Functions.Lowering
