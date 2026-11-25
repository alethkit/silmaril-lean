module

public import Silmaril.Languages.Starlark.Lists.Freeze.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists

open Silmaril.Languages.Starlark.Lists

private theorem canMark_iff {heap : Heap} {roots marked : List Address} {a : Address} :
    heap.canMark roots marked a = true ↔
      a ∈ roots ∨ ∃ parent ∈ marked, a ∈ heap.children parent := by
  simp [Heap.canMark, List.any_eq_true]

private theorem mark_sound (heap : Heap) (roots remaining marked : List Address)
    (live : ∀ a ∈ remaining, a < heap.size)
    (seen : ∀ a ∈ marked, Reaches heap roots a) :
    ∀ a ∈ heap.mark roots remaining marked, Reaches heap roots a := by
  rw [Heap.mark]
  split
  · exact seen
  next address found =>
    have mem := List.mem_of_find?_eq_some found
    have eligible := canMark_iff.mp (List.find?_some found)
    have reached : Reaches heap roots address := by
      rcases eligible with root | ⟨parent, visited, child⟩
      · exact .root (live address mem) root
      · exact .child (live address mem) (seen parent visited) child
    apply mark_sound heap roots (remaining.erase address) (address :: marked)
    · exact fun a h => live a (List.mem_of_mem_erase h)
    · intro a h
      rcases List.mem_cons.mp h with rfl | h
      · exact reached
      · exact seen a h
termination_by remaining.length
decreasing_by
  simp only [List.length_erase_of_mem mem]
  have positive := List.length_pos_of_mem mem
  omega

private theorem mark_closed (heap : Heap) (roots remaining marked : List Address)
    (cover : ∀ a, a < heap.size → a ∈ remaining ∨ a ∈ marked) :
    let result := heap.mark roots remaining marked
    (∀ a ∈ marked, a ∈ result) ∧
      (∀ a, a < heap.size → heap.canMark roots result a = true → a ∈ result) := by
  dsimp
  rw [Heap.mark]
  split
  next exhausted =>
    refine ⟨fun _ h => h, ?_⟩
    intro a live eligible
    rcases cover a live with remaining | visited
    · exact False.elim (List.find?_eq_none.mp exhausted a remaining eligible)
    · exact visited
  next address found =>
    have mem := List.mem_of_find?_eq_some found
    have cover' : ∀ a, a < heap.size → a ∈ remaining.erase address ∨ a ∈ address :: marked := by
      intro a live
      by_cases same : a = address
      · exact Or.inr (List.mem_cons.mpr (Or.inl same))
      · rcases cover a live with todo | seen
        · exact Or.inl ((List.mem_erase_of_ne same).mpr todo)
        · exact Or.inr (List.mem_cons_of_mem address seen)
    obtain ⟨preserved, closed⟩ := mark_closed heap roots (remaining.erase address)
      (address :: marked) cover'
    exact ⟨fun a h => preserved a (List.mem_cons_of_mem address h), closed⟩
termination_by remaining.length
decreasing_by
  simp only [List.length_erase_of_mem mem]
  have positive := List.length_pos_of_mem mem
  omega

theorem mark_iff (heap : Heap) (roots : List Address) (a : Address) :
    a ∈ heap.mark roots (List.range heap.size) [] ↔ Reaches heap roots a := by
  constructor
  · exact mark_sound heap roots _ _ (fun _ h => List.mem_range.mp h) (by simp)
      a
  · have closed := (mark_closed heap roots (List.range heap.size) []
      (fun _ live => Or.inl (List.mem_range.mpr live))).2
    intro reaches
    induction reaches with
    | root live root => exact closed _ live (canMark_iff.mpr (Or.inl root))
    | child live _ edge ih => exact closed _ live (canMark_iff.mpr (Or.inr ⟨_, ih, edge⟩))

theorem freezes_freeze (heap : Heap) (roots : List Address) :
    Freezes heap roots (heap.freeze roots) := by
  constructor
  · simp [Heap.freeze]
  · intro a before found
    refine ⟨before.frozen || (heap.mark roots (List.range heap.size) []).contains a, ?_, ?_⟩
    · simp [Heap.freeze, found]
    · simp [mark_iff]

theorem eq_freeze_of_freezes {heap after : Heap} {roots : List Address}
    (h : Freezes heap roots after) : heap.freeze roots = after := by
  apply Array.ext_getElem?
  intro a
  cases found : heap[a]? with
  | none =>
    rw [Array.getElem?_eq_none_iff] at found
    have absent : after[a]? = none := Array.getElem?_eq_none_iff.mpr (h.size_eq ▸ found)
    simp [Heap.freeze, Array.getElem?_eq_none_iff.mpr found, absent]
  | some before =>
    obtain ⟨expected, heapHit, expectedIff⟩ := (freezes_freeze heap roots).cell a before found
    obtain ⟨actual, afterHit, actualIff⟩ := h.cell a before found
    have eq : expected = actual := Bool.eq_iff_iff.mpr (expectedIff.trans actualIff.symm)
    rw [heapHit, afterHit, eq]

theorem updateCell_frozen (state : State) (address : Address)
    (edit : List Value → Except Error (List Value)) {cell : Cell}
    (found : state.heap[address]? = some cell) (frozen : cell.frozen = true) :
    updateCell address edit state =
      match edit cell.elements with
      | .ok _ => .error (.frozen address) state
      | .error error => .error error state := by
  cases checked : edit cell.elements <;>
    simp [updateCell, getCell, fromExcept, bind, EStateM.bind, found, checked, frozen] <;> rfl

end Silmaril.Proofs.Languages.Starlark.Lists
