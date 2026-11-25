module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSimultaneous.Window
import Mathlib.Tactic.Tauto

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {kind : VertexSeparation}
variable {d : Diagram S V W kind} {v z : Fin V} {lo hi : ℝ}

private theorem passing_block {cut : ℝ} {ids : List (Fin W)}
    (central : ∀ w ∈ ids, d.crosses w (d.vertexHeight v))
    (at_cut : ∀ w ∈ ids, d.crosses w cut)
    (ordered : ids.Pairwise (fun a b => d.x a (d.vertexHeight v) < d.x b (d.vertexHeight v))) :
    Block d (d.vertexHeight v) cut ids := by
  have cv (w : Fin W) (hw : w ∈ ids) : d.covers w (d.vertexHeight v) :=
    ⟨(central w hw).1.le, (central w hw).2.le⟩
  exact ⟨cv, at_cut, ordered.imp_of_mem fun ha hb h =>
    order_to_cut (cv _ ha) (cv _ hb) (at_cut _ ha) (at_cut _ hb) h⟩

private theorem select_passing : Nonempty (d.PassingWires v z) := by
  obtain ⟨left, le, ls⟩ := d.ordered_selection (d.vertexHeight v)
    (fun w => d.crosses w (d.vertexHeight v) ∧ d.x w (d.vertexHeight v) < d.vertexX v) (fun _ hw => hw.1)
  obtain ⟨mid, me, ms⟩ := d.ordered_selection (d.vertexHeight v)
    (fun w => d.crosses w (d.vertexHeight v) ∧
      d.vertexX v < d.x w (d.vertexHeight v) ∧ d.x w (d.vertexHeight v) < d.vertexX z)
    (fun _ hw => hw.1)
  obtain ⟨right, re, rs⟩ := d.ordered_selection (d.vertexHeight v)
    (fun w => d.crosses w (d.vertexHeight v) ∧ d.vertexX z < d.x w (d.vertexHeight v)) (fun _ hw => hw.1)
  exact ⟨⟨left, mid, right, le, me, re, ls, ms, rs⟩⟩

private theorem passing_exact (pair : d.IsolatesPair v z lo hi)
    (p : d.PassingWires v z) (w : Fin W) :
    d.crosses w (d.vertexHeight v) ↔ w ∈ p.left ∨ w ∈ p.middle ∨ w ∈ p.right := by
  rw [p.left_exact, p.middle_exact, p.right_exact]
  constructor
  · intro hw
    rcases lt_or_gt_of_ne (d.avoids_vertex w v hw) with left | afterLeft
    · exact Or.inl ⟨hw, left⟩
    · have hz : d.crosses w (d.vertexHeight z) := pair.same_height.symm ▸ hw
      have hne := d.avoids_vertex w z hz
      rw [pair.same_height] at hne
      rcases lt_or_gt_of_ne hne with mid | right
      · exact Or.inr (Or.inl ⟨hw, afterLeft, mid⟩)
      · exact Or.inr (Or.inr ⟨hw, right⟩)
  · tauto

private theorem assemble_cut (pair : d.IsolatesPair v z lo hi)
    (p : d.PassingWires v z) {cut : ℝ} {p₁ p₂ : List (Fin W)}
    (classify : ∀ w, d.crosses w cut ↔ d.crosses w (d.vertexHeight v) ∨ w ∈ p₁ ∨ w ∈ p₂)
    (port₁ : Block d (d.vertexHeight v) cut p₁) (port₂ : Block d (d.vertexHeight v) cut p₂)
    (pos₁ : ∀ w ∈ p₁, d.x w (d.vertexHeight v) = d.vertexX v)
    (pos₂ : ∀ w ∈ p₂, d.x w (d.vertexHeight v) = d.vertexX z) :
    d.OrderedCut cut ((p.left ++ (p₁ ++ p.middle)) ++ (p₂ ++ p.right)) := by
  have running (w : Fin W) (hw : d.crosses w (d.vertexHeight v)) : d.crosses w cut :=
    (classify w).mpr (Or.inl hw)
  have left := passing_block
    (fun w hw => ((p.left_exact w).mp hw).1)
    (fun w hw => running w ((p.left_exact w).mp hw).1) p.left_order
  have mid := passing_block
    (fun w hw => ((p.middle_exact w).mp hw).1)
    (fun w hw => running w ((p.middle_exact w).mp hw).1) p.middle_order
  have right := passing_block
    (fun w hw => ((p.right_exact w).mp hw).1)
    (fun w hw => running w ((p.right_exact w).mp hw).1) p.right_order
  have lm := port₁.append mid (fun a ha b hb => (pos₁ a ha).trans_lt ((p.middle_exact b).mp hb).2.1)
  have first := left.append lm (by
    intro a ha b hb
    have h := ((p.left_exact a).mp ha).2
    rcases List.mem_append.mp hb with hb | hb
    · exact h.trans_eq (pos₁ b hb).symm
    · exact h.trans ((p.middle_exact b).mp hb).2.1)
  have second := port₂.append right (fun a ha b hb => (pos₂ a ha).trans_lt ((p.right_exact b).mp hb).2)
  have full := first.append second (by
    intro a ha b hb
    have a_left : d.x a (d.vertexHeight v) < d.vertexX z := by
      rcases List.mem_append.mp ha with ha | ha
      · exact (((p.left_exact a).mp ha).2).trans pair.left_to_right
      · rcases List.mem_append.mp ha with ha | ha
        · exact (pos₁ a ha).trans_lt pair.left_to_right
        · exact ((p.middle_exact a).mp ha).2.2
    rcases List.mem_append.mp hb with hb | hb
    · exact a_left.trans_eq (pos₂ b hb).symm
    · exact a_left.trans ((p.right_exact b).mp hb).2)
  refine ⟨?_, full.ordered⟩
  intro w
  rw [classify, passing_exact pair p w]
  simp only [List.mem_append]
  tauto

theorem simultaneous_event (pair : d.IsolatesPair v z lo hi) : Nonempty (d.PairSlice v z lo hi) := by
  obtain ⟨p⟩ := select_passing (d := d) (v := v) (z := z)
  refine ⟨⟨p, pair, ?_, ?_⟩⟩
  · refine assemble_cut pair p (before_classify pair)
      (layer_incoming pair.toLayer rfl) (layer_incoming pair.toLayer pair.same_height) ?_ ?_
    · intro w hw
      exact d.finish_attached w v ((input_mem v w).mp hw)
    · intro w hw
      rw [← pair.same_height]
      exact d.finish_attached w z ((input_mem z w).mp hw)
  · refine assemble_cut pair p (after_classify pair)
      (layer_outgoing pair.toLayer rfl) (layer_outgoing pair.toLayer pair.same_height) ?_ ?_
    · intro w hw
      exact d.start_attached w v ((output_mem v w).mp hw)
    · intro w hw
      rw [← pair.same_height]
      exact d.start_attached w z ((output_mem z w).mp hw)

end Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous
