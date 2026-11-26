module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination

open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback (Graph)
open Relation (ReflTransGen TransGen)

universe u v

variable {P : Type u} {O : Type v} {g : Graph P O} {inside : P → Prop} {p q : P}

theorem close_top_iff : g.close p = ⊤ ↔ g.ReachesUB p := by
  classical
  by_cases h : g.ReachesUB p <;> simp [Graph.close, h]

theorem close_of_safe (h : ¬ g.ReachesUB p) : g.close p = ↑(g.outcomes p) := by
  classical
  simp [Graph.close, h]

theorem ordinary_close_iff {o : O} : g.Ordinary p o ↔ ¬ g.ReachesUB p ∧ o ∈ g.outcomes p := by
  classical
  by_cases h : g.ReachesUB p <;> simp [Graph.Ordinary, Graph.close, h]

/-- Each ordinary outer transfer has an inner prefix and a final genuine edge. -/
theorem outer_step_iff :
    (g.outer inside).step p q ↔
      ¬ (g.inner inside).ReachesUB p ∧
        ∃ b, (g.inner inside).Reaches p b ∧ g.step b q ∧ ¬ inside q := by
  change (g.inner inside).Ordinary p (.inl q) ↔ _
  rw [ordinary_close_iff]
  simp only [Graph.outcomes, Set.mem_ofPred_eq, Graph.inner, reduceCtorEq, false_and, or_false]
  rfl

theorem outer_finish_iff {o : O} :
    (g.outer inside).finish p o ↔
      ¬ (g.inner inside).ReachesUB p ∧
        ((g.inner inside).Finite p (.inr o) ∨ o = g.divergence ∧ (g.inner inside).Infinite p) := by
  change (g.inner inside).Ordinary p (.inr o) ↔ _
  rw [ordinary_close_iff]
  simp only [Graph.outcomes, Set.mem_ofPred_eq, Graph.inner, Sum.inr.injEq]

theorem inner_reaches_flat (h : (g.inner inside).Reaches p q) : g.Reaches p q :=
  ReflTransGen.mono (fun _ _ edge => edge.1) _ _ h

theorem outer_step_progress (h : (g.outer inside).step p q) : TransGen g.step p q := by
  obtain ⟨_, b, path, edge, _⟩ := outer_step_iff.mp h
  exact TransGen.tail' (inner_reaches_flat path) edge

theorem outer_reaches_flat (h : (g.outer inside).Reaches p q) : g.Reaches p q :=
  h.trans_induction_on (fun _ => .refl) (fun edge => (outer_step_progress edge).to_reflTransGen)
    (fun _ _ first rest => first.trans rest)

theorem inner_safe (safe : ¬ g.ReachesUB p) (path : g.Reaches p q) :
    ¬ (g.inner inside).ReachesUB q :=
  fun ⟨b, tail, ub⟩ => safe ⟨b, path.trans (inner_reaches_flat tail), ub⟩

/-- Segment a finite flat path. At an earlier outer point, inner UB may
suppress its ordinary continuation. That point already witnesses outer UB. -/
theorem split_reaches (h : g.Reaches p q) :
    (g.outer inside).ReachesUB p ∨
      ∃ b, (g.outer inside).Reaches p b ∧ (g.inner inside).Reaches b q := by
  classical
  induction h with
  | refl => exact Or.inr ⟨p, .refl, .refl⟩
  | @tail _ target _ edge ih =>
    rcases ih with ub | ⟨b, earlier, pending⟩
    · exact Or.inl ub
    by_cases internal : inside target
    · exact Or.inr ⟨b, earlier, pending.tail ⟨edge, internal⟩⟩
    by_cases ub : (g.inner inside).ReachesUB b
    · exact Or.inl ⟨b, earlier, close_top_iff.mpr ub⟩
    · exact Or.inr ⟨_, earlier.tail (outer_step_iff.mpr ⟨ub, _, pending, edge, internal⟩), .refl⟩

theorem reachesUB_outer_iff : (g.outer inside).ReachesUB p ↔ g.ReachesUB p := by
  constructor
  · rintro ⟨b, path, ub⟩
    obtain ⟨q, tail, top⟩ := close_top_iff.mp ub
    exact ⟨q, (outer_reaches_flat path).trans (inner_reaches_flat tail), top⟩
  · rintro ⟨q, path, top⟩
    rcases split_reaches (inside := inside) path with ub | ⟨b, earlier, pending⟩
    · exact ub
    · exact ⟨b, earlier, close_top_iff.mpr ⟨q, pending, top⟩⟩

/-- Finite paths to terminal observations segment exactly below UB. Neither
side of this comparison introduces divergence from an infinite path. -/
theorem finite_segmented_iff {o : O} (safe : ¬ g.ReachesUB p) :
    g.Finite p o ↔ ∃ b, (g.outer inside).Reaches p b ∧ (g.inner inside).Finite b (.inr o) := by
  constructor
  · rintro ⟨q, path, finish⟩
    rcases split_reaches (inside := inside) path with ub | ⟨b, earlier, pending⟩
    · exact (safe (reachesUB_outer_iff.mp ub)).elim
    · exact ⟨b, earlier, q, pending, finish⟩
  · rintro ⟨b, path, q, tail, finish⟩
    exact ⟨q, (outer_reaches_flat path).trans (inner_reaches_flat tail), finish⟩

theorem finite_to_outer {o : O} (safe : ¬ g.ReachesUB p) (h : g.Finite p o) :
    (g.outer inside).Finite p o := by
  obtain ⟨b, path, finish⟩ := (finite_segmented_iff (inside := inside) safe).mp h
  exact ⟨b, path, outer_finish_iff.mpr ⟨inner_safe safe (outer_reaches_flat path), Or.inl finish⟩⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination
