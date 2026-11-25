module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveSimultaneous.Window
import Mathlib.Tactic.Tauto

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {kind : VertexSeparation}
variable {d : Diagram S V W kind} {v z : Fin V} {lo hi : ℝ}

/-- A list with points at the central height and with a strict order at the cut. -/
private structure Block (d : Diagram S V W kind) (event cut : ℝ) (ids : List (Fin W)) : Prop where
  covers : ∀ w ∈ ids, d.covers w event
  crosses : ∀ w ∈ ids, d.crosses w cut
  ordered : ids.Pairwise (fun a b => d.x a cut < d.x b cut)

private theorem Block.append {event cut : ℝ} {l r : List (Fin W)}
    (a : Block d event cut l) (b : Block d event cut r)
    (h : ∀ w ∈ l, ∀ z ∈ r, d.x w event < d.x z event) :
    Block d event cut (l ++ r) := by
  exact ⟨fun w hw => (List.mem_append.mp hw).elim (a.covers w) (b.covers w),
    fun w hw => (List.mem_append.mp hw).elim (a.crosses w) (b.crosses w),
    List.pairwise_append.mpr ⟨a.ordered, b.ordered, fun w hw z hz =>
      order_to_cut (a.covers w hw) (b.covers z hz) (a.crosses w hw) (b.crosses z hz) (h w hw z hz)⟩⟩

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

private theorem incoming (pair : d.IsolatesPair v z lo hi) {j : Fin V}
    (hj : j = v ∨ j = z) :
    Block d (d.vertexHeight v) lo (d.inputs j) := by
  have height : d.vertexHeight j = d.vertexHeight v := by
    rcases hj with rfl | rfl
    · rfl
    · exact pair.same_height
  have crosses (w : Fin W) (hw : w ∈ d.inputs j) : d.crosses w lo := by
    apply (before_classify pair w).mpr
    rcases hj with rfl | rfl
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr hw)
  refine ⟨fun w hw => ?_, crosses, List.pairwise_ofFn.mpr ?_⟩
  · have upper := (finish_height ((input_mem j w).mp hw)).trans height
    exact ⟨(crosses w hw).1.le.trans pair.below.le, upper.ge⟩
  · intro a b hab
    have ha := crosses _ (List.mem_ofFn.mpr ⟨a, rfl⟩)
    have hb := crosses _ (List.mem_ofFn.mpr ⟨b, rfl⟩)
    exact d.input_order j hab ha.1 hb.1 (pair.below.trans_eq height.symm)

private theorem outgoing (pair : d.IsolatesPair v z lo hi) {j : Fin V}
    (hj : j = v ∨ j = z) :
    Block d (d.vertexHeight v) hi (d.outputs j) := by
  have height : d.vertexHeight j = d.vertexHeight v := by
    rcases hj with rfl | rfl
    · rfl
    · exact pair.same_height
  have crosses (w : Fin W) (hw : w ∈ d.outputs j) : d.crosses w hi := by
    apply (after_classify pair w).mpr
    rcases hj with rfl | rfl
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr hw)
  refine ⟨fun w hw => ?_, crosses, List.pairwise_ofFn.mpr ?_⟩
  · have lower := (start_height ((output_mem j w).mp hw)).trans height
    exact ⟨lower.le, pair.above.le.trans (crosses w hw).2.le⟩
  · intro a b hab
    have ha := crosses _ (List.mem_ofFn.mpr ⟨a, rfl⟩)
    have hb := crosses _ (List.mem_ofFn.mpr ⟨b, rfl⟩)
    exact d.output_order j hab (height.trans_lt pair.above) ha.2 hb.2

theorem simultaneous_event (pair : d.IsolatesPair v z lo hi) : Nonempty (d.PairSlice v z lo hi) := by
  obtain ⟨p⟩ := select_passing (d := d) (v := v) (z := z)
  refine ⟨⟨p, pair, ?_, ?_⟩⟩
  · refine assemble_cut pair p (before_classify pair)
      (incoming pair (Or.inl rfl)) (incoming pair (Or.inr rfl)) ?_ ?_
    · intro w hw
      exact d.finish_attached w v ((input_mem v w).mp hw)
    · intro w hw
      rw [← pair.same_height]
      exact d.finish_attached w z ((input_mem z w).mp hw)
  · refine assemble_cut pair p (after_classify pair)
      (outgoing pair (Or.inl rfl)) (outgoing pair (Or.inr rfl)) ?_ ?_
    · intro w hw
      exact d.start_attached w v ((output_mem v w).mp hw)
    · intro w hw
      rw [← pair.same_height]
      exact d.start_attached w z ((output_mem z w).mp hw)

end Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous
