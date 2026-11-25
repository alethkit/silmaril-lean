module

public import Silmaril.Proofs.Semantics.RuntimeWires.SeamTrace.Bijection

public section

namespace Silmaril.RuntimeWires.Proofs.SeamTrace

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

private def uses (sites : Set BoxAddress) : WireOrigin → Prop
  | .boundary _ => True
  | .box row ordinal _ => (row, ordinal) ∈ sites

private def wireListUses (sites : Set BoxAddress) (wires : List (NamedWire O)) : Prop :=
  ∀ w ∈ wires, uses sites w.2

private theorem boundary_uses (sites : Set BoxAddress) (word : List O) :
    wireListUses sites (namePorts .boundary word) := by
  intro w hw
  obtain ⟨⟨label, port⟩, _, rfl⟩ := List.mem_map.mp hw
  trivial

private theorem box_uses {sites : Set BoxAddress} {row box : ℕ} (h : (row, box) ∈ sites)
    (word : List O) : wireListUses sites (namePorts (.box row box) word) := by
  intro w hw
  obtain ⟨⟨label, port⟩, _, rfl⟩ := List.mem_map.mp hw
  exact h

private theorem row_uses {A B : List O} (r : Row S A B) (sites : Set BoxAddress)
    (row first : ℕ) (input : List (NamedWire O)) (ins : wireListUses sites input)
    (addresses : ∀ i < (r.traceWires row first input).boxes.length, (row, first + i) ∈ sites) :
    let trace := r.traceWires row first input
    wireListUses sites trace.frontier ∧
      ∀ box ∈ trace.boxes, wireListUses sites (box.inputs ++ box.outputs) := by
  induction r generalizing first input with
  | empty => simp [Row.traceWires, wireListUses]
  | wire x r ih =>
    have tail := ih first input.tail (fun w hw => ins w (List.tail_sublist _ |>.subset hw)) addresses
    refine ⟨?_, tail.2⟩
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact ins w (List.mem_of_mem_take h)
    · exact tail.1 w h
  | box e r ih =>
    have ports := box_uses (by simpa using addresses 0 (by simp [Row.traceWires])) (S.target e)
    have rest := ih (first + 1) (input.drop (S.source e).length)
      (fun w hw => ins w (List.mem_of_mem_drop hw)) (fun i hi => by
        have eq : first + 1 + i = first + (i + 1) := by omega
        rw [eq]
        exact addresses (i + 1) (Nat.succ_lt_succ hi))
    constructor
    · intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact ports w h
      · exact rest.1 w h
    · intro b hb w hw
      rcases List.mem_cons.mp hb with eq | other
      · subst b
        rcases List.mem_append.mp hw with h | h
        · exact ins w (List.mem_of_mem_take h)
        · exact ports w h
      · exact rest.2 b other w hw

private theorem box_of_address {row first : ℕ} {boxes : List (BoxTrace S)} {entry : BoxOccurrence S}
    (h : entry ∈ addressBoxes row first boxes) : entry.2 ∈ boxes := by
  induction boxes generalizing first with
  | nil => simp [addressBoxes] at h
  | cons box boxes ih =>
    rcases List.mem_cons.mp h with eq | tail
    · exact List.mem_cons.mpr (.inl (congrArg Prod.snd eq))
    · exact .tail _ (ih tail)

private theorem sheet_uses {A B : List O} (p : Sheet S A B) (sites : Set BoxAddress)
    (row : ℕ) (input : List (NamedWire O)) (ins : wireListUses sites input)
    (addresses : ∀ site ∈ (addressRows row (p.traceWiresFrom row input).rows).map Prod.fst, site ∈ sites) :
    let trace := p.traceWiresFrom row input
    wireListUses sites trace.outputs ∧
      ∀ entry ∈ addressRows row trace.rows, wireListUses sites (entry.2.inputs ++ entry.2.outputs) := by
  induction p generalizing row input with
  | empty => exact ⟨ins, by simp [Sheet.traceWiresFrom, addressRows]⟩
  | cons r p ih =>
    let head := r.traceWires row 0 input
    have now := row_uses r sites row 0 input ins (fun i hi => by
      apply addresses
      simp only [Sheet.traceWiresFrom, addressRows, List.map_append]
      exact List.mem_append_left _ (mem_row_addresses.mpr ⟨rfl, Nat.zero_le _, by simpa using hi⟩))
    have later := ih (row + 1) head.frontier now.1 (fun site h => by
      apply addresses
      simp only [Sheet.traceWiresFrom, addressRows, List.map_append]
      exact List.mem_append_right _ h)
    refine ⟨later.1, ?_⟩
    intro entry mem
    rcases List.mem_append.mp mem with e | e
    · exact now.2 _ (box_of_address e)
    · exact later.2 entry e

private theorem map_id_on {α : Type*} (l : List α) (f : α → α) (h : ∀ x ∈ l, f x = x) :
    l.map f = l :=
  (List.map_congr_left (g := id) h).trans (List.map_id _)

private theorem roundtrip_wireList {sites : Set BoxAddress} {route back : BoxAddress → BoxAddress}
    (inverse : Set.LeftInvOn back route sites) (wires : List (NamedWire O)) (h : wireListUses sites wires) :
    (wires.map (NamedWire.rename route)).map (NamedWire.rename back) = wires := by
  rw [List.map_map]
  apply map_id_on
  rintro ⟨label, w⟩ mem
  have valid := h _ mem
  cases w with
  | boundary => rfl
  | box row box port =>
    change (label, WireOrigin.box (back (route (row, box))).1 (back (route (row, box))).2 port) = _
    rw [inverse valid]

theorem inverse_trace {A B : List O} (p : Sheet S A B) {right : SheetTrace S}
    {route back : BoxAddress → BoxAddress}
    (matchTrace : p.traceWires.Renamed right route)
    (inverse : Set.LeftInvOn back route p.traceWires.boxAddresses) :
    right.Renamed p.traceWires back := by
  let trace := p.traceWires
  let sites := trace.boxAddresses
  have support := sheet_uses p sites 0 (namePorts .boundary A) (boundary_uses sites A)
    (fun _ h => h)
  have boxes : ((trace.occurrences.map (BoxOccurrence.rename route)).map (BoxOccurrence.rename back)) =
      trace.occurrences := by
    rw [List.map_map]
    apply map_id_on
    rintro ⟨site, box⟩ mem
    have atSite : site ∈ sites := List.mem_map.mpr ⟨(site, box), mem, rfl⟩
    have ports := support.2 (site, box) mem
    have inputs := roundtrip_wireList inverse box.inputs
      (fun w hw => ports w (List.mem_append_left _ hw))
    have outputs := roundtrip_wireList inverse box.outputs
      (fun w hw => ports w (List.mem_append_right _ hw))
    rcases box with ⟨label, ins, outs⟩
    simp only [Function.comp_apply, BoxOccurrence.rename, BoxTrace.rename]
    rw [inverse atSite, inputs, outputs]
  constructor
  · change (right.occurrences.map (BoxOccurrence.rename back)).Perm trace.occurrences
    have h := matchTrace.occurrences.symm.map (BoxOccurrence.rename back)
    change (right.occurrences.map (BoxOccurrence.rename back)).Perm
      ((trace.occurrences.map (BoxOccurrence.rename route)).map (BoxOccurrence.rename back)) at h
    rwa [boxes] at h
  · rw [← matchTrace.outputs]
    exact roundtrip_wireList inverse trace.outputs support.1

end Silmaril.RuntimeWires.Proofs.SeamTrace
