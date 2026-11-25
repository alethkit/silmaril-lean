module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Thms
import Mathlib.Order.Hom.Set

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.CapRecoordination

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : CapProfile O}
variable (p : FixedDrawing S a b) (hp : p.vertices = 0)
include hp

theorem no_vertex (j : Fin p.vertices) : False := (Fin.cast hp j).elim0

theorem start_none (w : Fin p.wires) : p.drawing.start w = none := by
  cases p.drawing.start w with
  | none => rfl
  | some j => exact (no_vertex p hp j).elim

theorem finish_none (w : Fin p.wires) : p.drawing.finish w = none := by
  cases p.drawing.finish w with
  | none => rfl
  | some j => exact (no_vertex p hp j).elim

def inputWires : Fin a.size ≃ Fin p.wires :=
  p.input.trans (Equiv.subtypeUnivEquiv (start_none p hp))

def outputWires : Fin b.size ≃ Fin p.wires :=
  p.output.trans (Equiv.subtypeUnivEquiv (finish_none p hp))

theorem covers (w : Fin p.wires) (y : ℝ) :
    p.drawing.covers w y ↔ y ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [Diagram.covers, Diagram.lower, Diagram.upper, endpointHeight,
    start_none p hp, finish_none p hp, Option.elim_none]

theorem wire_continuous (w : Fin p.wires) :
    ContinuousOn (p.drawing.x w) (Set.Icc (0 : ℝ) 1) := by
  change ContinuousOn (p.drawing.wire w).x _
  simpa only [endpointHeight, start_none p hp, finish_none p hp, Option.elim_none]
    using (p.drawing.wire w).continuous

/-- With no vertices, all wires span the unit interval. Their cap order
cannot change as the height varies. -/
theorem ordered {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    StrictMono (fun i => p.drawing.x (inputWires p hp i) y) := by
  intro i j ij
  let w := inputWires p hp i
  let z := inputWires p hp j
  have distinct : w ≠ z := fun eq => ij.ne ((inputWires p hp).injective eq)
  have atBottom : p.drawing.x w 0 < p.drawing.x z 0 :=
    (p.input_x i).symm ▸ (p.input_x j).symm ▸ a.ordered ij
  have heights : Set.uIcc 0 y ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hy.1]
    exact Set.Icc_subset_Icc_right hy.2
  apply p.drawing.order_across (w := w) (z := z) (a := 0) (b := y) ?_ ?_ atBottom
  · exact fun t ht => ⟨(covers p hp w t).mpr (heights ht), (covers p hp z t).mpr (heights ht)⟩
  · intro t ht
    rcases (heights ht).1.eq_or_lt with h | h
    · exact h ▸ p.drawing.input_boundary_separated distinct (start_none p hp w) (start_none p hp z)
    rcases (heights ht).2.eq_or_lt with h' | h'
    · exact h'.symm ▸ p.drawing.output_boundary_separated distinct (finish_none p hp w) (finish_none p hp z)
    · apply p.drawing.separated distinct
      · simpa only [endpointHeight, start_none p hp, finish_none p hp, Option.elim_none]
          using (show t ∈ Set.Ioo (0 : ℝ) 1 from ⟨h, h'⟩)
      · exact (covers p hp z t).mpr (heights ht)

def slotEquiv : Fin a.size ≃ Fin b.size :=
  (inputWires p hp).trans (outputWires p hp).symm

theorem top_at_slot (i : Fin a.size) :
    p.drawing.x (inputWires p hp i) 1 = b.x (slotEquiv p hp i) := by
  rw [← p.output_x (slotEquiv p hp i)]
  change p.drawing.x (inputWires p hp i) 1 =
    p.drawing.x (outputWires p hp ((outputWires p hp).symm (inputWires p hp i))) 1
  rw [Equiv.apply_symm_apply]

/-- The top slot of a through strand is uniquely determined by its bottom
slot, since it gives an increasing bijection of finite ordered slots. -/
def slotOrder : Fin a.size ≃o Fin b.size where
  toEquiv := slotEquiv p hp
  map_rel_iff' {i j} := by
    rw [← b.ordered.le_iff_le, ← top_at_slot, ← top_at_slot]
    exact (ordered p hp ⟨zero_le_one, le_rfl⟩).le_iff_le

theorem same_top (q : FixedDrawing S a b) (hq : q.vertices = 0) (i : Fin a.size) :
    p.drawing.x (inputWires p hp i) 1 = q.drawing.x (inputWires q hq i) 1 := by
  have h : slotOrder p hp = slotOrder q hq := Subsingleton.elim _ _
  exact (top_at_slot p hp i).trans <|
    (congrArg (fun e : Fin a.size ≃o Fin b.size => b.x (e i)) h).trans (top_at_slot q hq i).symm

end Silmaril.RuntimeWires.Proofs.CapRecoordination
