module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Proofs

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Merge Projection Slot)

universe u

theorem latch_publish_iff {α : Type u} (merge : Merge) (arrival : Slot) (edge : Projection)
    (exported selected : α) :
    latch merge arrival (publish edge exported) = some selected ↔
      merge.predecessor arrival = edge ∧ exported = selected := by
  unfold latch publish
  by_cases isEdge : merge.predecessor arrival = edge <;> simp [isEdge]

theorem latch_publish_slot {α : Type u} (merge : Merge) (edge : Projection) (value : α) :
    latch merge (merge.slot edge) (publish edge value) = some value :=
  (latch_publish_iff merge (merge.slot edge) edge value value).mpr
    ⟨merge.predecessor_slot edge, rfl⟩

private theorem taken_iff (guard : Bool) (edge : Projection) :
    Projection.Taken guard edge ↔ Projection.ofBool guard = edge := by
  constructor
  · intro taken
    cases taken <;> rfl
  · intro selected
    cases guard <;> cases selected
    · exact .onFalse
    · exact .onTrue

theorem returns_iff_denote {args : List ValueSort} {cells : Nat} (graph : Graph args)
    (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells)
    (value : Word) (final : Heap cells) :
    graph.Returns guard input initial value final ↔
      graph.denote guard input initial = (value, final) := by
  constructor
  · intro run
    cases run with
    | @ret edge arrival exported selected _ _ taken arm joined suffix =>
      have edgeEq := (taken_iff guard edge).mp taken
      have payloadEq := ((latch_publish_iff graph.merge arrival edge exported selected).mp joined).2
      have armEq := ((graph.arm edge).returns_iff_denote input initial exported.1 exported.2).mp arm
      subst selected
      simpa only [Graph.denote, edgeEq, armEq] using
        (graph.suffix.returns_iff_denote _ _ value final).mp suffix
  · intro result
    let edge := Projection.ofBool guard
    let exported := (graph.arm edge).denote input initial
    exact .ret (arrival := graph.merge.slot edge) (exported := exported) (selected := exported)
      ((taken_iff guard edge).mpr rfl)
      (((graph.arm edge).returns_iff_denote input initial exported.1 exported.2).mpr rfl)
      (latch_publish_slot graph.merge edge exported)
      ((graph.suffix.returns_iff_denote _ _ value final).mpr result)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Proofs
