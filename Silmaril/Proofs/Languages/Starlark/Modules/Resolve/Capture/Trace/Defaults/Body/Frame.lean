module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Heap
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Capture Value)

theorem root_free {owned globals : List String} {reads : List Binding} {free : List FreeName}
    (selected : Selects ⟨owned, [], globals⟩ reads free) (entry : FreeName) (present : entry ∈ free) :
    ∃ name ∈ globals, entry = ⟨globalSlot name, globalSlot name⟩ := by
  induction selected with
  | nil => cases present
  | owned _ _ ih => exact ih present
  | enclosing origin selection ih =>
    cases origin with
    | enclosing _ impossible => cases impossible
  | module origin _ ih =>
    rcases List.mem_cons.mp present with rfl | later
    · cases origin with
      | module _ _ known => exact ⟨_, known, rfl⟩
    · exact ih later

theorem instantiates {globals : List String} {definition : Definition} (plan : Plan globals definition)
    (caller : State) (layout : ModuleSlots globals caller) :
    ∃ captures, Installs caller plan.free captures := by
  apply Forwarding.installs_of_addresses
  intro entry member
  obtain ⟨name, known, rfl⟩ := root_free plan.selects entry member
  obtain ⟨address, _, _, owned, _⟩ := layout.usable name known
  exact ⟨globalSlot name, address, rfl, .inl owned⟩

theorem keeps_installation {old next : State} {free : List FreeName} {captures : List Capture}
    (slots : next.slots = old.slots) (installed : Installs old free captures) :
    Installs next free captures := by
  induction installed with
  | nil => exact .nil
  | cons received _ ih =>
    cases received with
    | enclosing proof => exact .cons (.enclosing (slots ▸ proof)) ih
    | forwardedLocal proof => exact .cons (.forwardedLocal (slots ▸ proof)) ih
    | ownedGlobal proof => exact .cons (.ownedGlobal (slots ▸ proof)) ih
    | capturedGlobal proof => exact .cons (.capturedGlobal (slots ▸ proof)) ih

/-- The generic frame theorem accepts owned or forwarded captures whose
address has a live binding cell in the current caller heap. -/
theorem activate_frame (block : LexicalBlock) (declaration : Declaration)
    (slots : declaration.signature.slots ++ declaration.locals = block.owned.map fileSlot)
    (caller : State) (captures : List Capture) (assigned : List (Binding × Value))
    (selected : ∀ binding, (⟨binding, binding⟩ : FreeName) ∈ declaration.free →
      binding ∉ declaration.signature.slots ++ declaration.locals ∧
      ∃ capture, captures.find? (fun entry => entry.binding == binding) = some capture ∧
        capture.binding = binding ∧ capture.localCell = (binding.scope == .local) ∧
        ∃ value frozen, caller.heap[capture.address]? = some ⟨.binding value, frozen⟩) :
    Frame block declaration.free caller.heap.size (activate caller declaration captures assigned) := by
  let active := activate caller declaration captures assigned
  have usable := Entry.activate_owned_cells caller declaration captures assigned
  constructor
  · intro name known
    have member : fileSlot name ∈ declaration.signature.slots ++ declaration.locals := by
      rw [slots]
      exact List.mem_map_of_mem known
    obtain ⟨address, owned⟩ := Capture.activate_owned caller declaration captures assigned _ member
    obtain ⟨value, frozen, stored⟩ := usable _ _ owned
    exact ⟨address, value, frozen, Wrapper.activation_fresh caller declaration captures assigned _ _ owned, owned, stored⟩
  · intro binding known
    obtain ⟨outside, capture, found, same, flag, value, frozen, stored⟩ := selected binding known
    have below := (Array.getElem?_eq_some_iff.mp stored).choose
    have own := Capture.activate_capture caller declaration captures capture assigned
      (by simpa only [same] using found) (by simpa only [same] using outside)
    rw [same, flag] at own
    exact ⟨capture.address, value, frozen, below, own,
      (Wrapper.activation_preserves caller declaration captures assigned _ below).trans stored⟩

theorem root_frame {globals : List String} {definition : Definition} (plan : Plan globals definition)
    (codes : List Lowering.Expr) (length : codes.length = definition.parameters.optional.length)
    (caller : State) (layout : ModuleSlots globals caller)
    (captures : List Capture) (installed : Installs caller plan.free captures) (assigned : List (Binding × Value)) :
    Frame plan.block plan.free caller.heap.size (activate caller (plan.declaration codes) captures assigned) := by
  have slots : (plan.declaration codes).signature.slots ++ (plan.declaration codes).locals =
      plan.block.owned.map fileSlot := by
    have named := List.map_fst_zip (l₁ := definition.parameters.optional.map (fileSlot ∘ Prod.fst))
      (l₂ := codes) (by simp [length])
    simp [Plan.declaration, Plan.block, Defaults.Parameters.signature, Defaults.Parameters.names,
      Signature.slots, Signature.named, requiredSignature, List.map_map, Function.comp_def] at named ⊢
    rw [named]
  apply activate_frame _ _ slots
  intro binding known
  obtain ⟨name, declared, entry⟩ := root_free plan.selects _ known
  have scope : binding = globalSlot name := congrArg FreeName.target entry
  subst binding
  refine ⟨?_, ?_⟩
  · rw [slots]
    simp [fileSlot, globalSlot]
  · obtain ⟨capture, found, nameEq, received⟩ := Forwarding.find_receipt installed (globalSlot name) known
    obtain ⟨address, value, frozen, owned, stored⟩ := layout.usable name declared
    cases received with
    | ownedGlobal cell =>
      have equal := Option.some.inj (cell.symm.trans owned)
      cases equal
      exact ⟨_, found, nameEq, rfl, _, _, stored⟩
    | capturedGlobal cell =>
      rw [owned] at cell
      cases cell

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body
