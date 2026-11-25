module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarDefs
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {W : ℕ}

theorem interpolate_lt {a b c d y : ℝ} (ha : a < c) (hb : b < d) (hy : y ∈ Set.Icc 0 1) :
    interpolate a b y < interpolate c d y := by
  rcases hy with ⟨nonnegative, atMostOne⟩
  rcases nonnegative.eq_or_lt with rfl | positive
  · simpa [interpolate] using ha
  · unfold interpolate
    nlinarith [mul_nonneg (sub_nonneg.mpr atMostOne) (sub_nonneg.mpr ha.le),
      mul_pos positive (sub_pos.mpr hb)]

theorem interpolate_inside {a b y : ℝ} (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1)
    (hy : y ∈ Set.Icc 0 1) : interpolate a b y ∈ Set.Ioo 0 1 := by
  refine ⟨?_, ?_⟩
  · simpa [interpolate] using interpolate_lt ha.1 hb.1 hy
  · have e : interpolate 1 1 y = 1 := by unfold interpolate; ring
    exact e ▸ interpolate_lt ha.2 hb.2 hy

theorem collar_order (c : CollarSpec O W) {a b : Fin W} {y : ℝ}
    (hy : y ∈ Set.Icc 0 1) :
    interpolate (c.bottom a) (c.top a) y < interpolate (c.bottom b) (c.top b) y ↔
      c.bottom a < c.bottom b := by
  refine ⟨fun h => ?_, fun h => interpolate_lt h ((c.order a b).mp h) hy⟩
  rcases lt_trichotomy (c.bottom a) (c.bottom b) with lt | eq | gt
  · exact lt
  · cases c.bottom_injective eq
    exact (lt_irrefl _ h).elim
  · exact ((interpolate_lt gt ((c.order b a).mp gt) hy).not_ge h.le).elim

theorem collar_separate (c : CollarSpec O W) {a b : Fin W} (ne : a ≠ b)
    {y : ℝ} (hy : y ∈ Set.Icc 0 1) :
    interpolate (c.bottom a) (c.top a) y ≠ interpolate (c.bottom b) (c.top b) y := by
  rcases lt_or_gt_of_ne (fun h => ne (c.bottom_injective h)) with h | h
  · exact ((collar_order c hy).mpr h).ne
  · exact ((collar_order c hy).mpr h).ne'

noncomputable def collarWire (c : CollarSpec O W) (w : Fin W) : Wire 0 1 where
  x := interpolate (c.bottom w) (c.top w)
  increasing := by norm_num
  continuous := by unfold interpolate; fun_prop
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    unfold interpolate
    ring

noncomputable def collarDrawing (c : CollarSpec O W) : Diagram S 0 W .point where
  vertexX := Fin.elim0
  vertexHeight := Fin.elim0
  vertex_inside := fun v => v.elim0
  vertex_separation := fun {a} => a.elim0
  generator := Fin.elim0
  label := c.label
  start := fun _ => none
  finish := fun _ => none
  wire := collarWire c
  wire_inside w _ h := interpolate_inside (c.bottom_inside w) (c.top_inside w) h
  start_attached _ := fun v => v.elim0
  finish_attached _ := fun v => v.elim0
  separated ne _ h _ := collar_separate c ne (Set.Ioo_subset_Icc_self h)
  avoids_vertex _ := fun v => v.elim0
  input_boundary_separated ne _ _ := collar_separate c ne (by norm_num [Set.mem_Icc])
  output_boundary_separated ne _ _ := collar_separate c ne (by norm_num [Set.mem_Icc])
  input := fun v => v.elim0
  output := fun v => v.elim0
  input_exact := fun v => v.elim0
  output_exact := fun v => v.elim0
  input_types := fun v => v.elim0
  output_types := fun v => v.elim0
  input_order := fun v => v.elim0
  output_order := fun v => v.elim0

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
