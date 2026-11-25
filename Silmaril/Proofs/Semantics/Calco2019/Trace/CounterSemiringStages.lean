module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Stages.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

public section

universe a b u v

namespace Silmaril.Calco2019.Proofs.CounterSemiringStages

open Silmaril.Calco2019.CounterSemiring
open Function

variable {A : Type a} {B : Type b} {U : Type u} {V : Type v}

theorem feedback_partition [Fintype U] [Fintype V] [DecidableEq V] (e : U ↪ V)
    (inner : Finset V) (sep : Disjoint (Finset.univ.map e) inner)
    (cover : Finset.univ.map e ∪ inner = Finset.univ) (f : Network A B V) :
    networkFeedback (retained e inner f) = networkFeedback f := by
  funext x y
  unfold networkFeedback retained
  have h := eliminateStates_reindex (A' := A) (B' := B) Finset.univ e
    (Sum.map id e) (Sum.map id e) (fun _ => rfl) (fun _ => rfl) (eliminateStates inner f)
  rw [h, ← eliminateStates_union _ _ sep, cover]
  rfl

variable [Fintype U] [Fintype V]

private theorem inl_inr_disjoint :
    Disjoint (Finset.univ.map (Embedding.inl : U ↪ U ⊕ V))
      (Finset.univ.map (Embedding.inr : V ↪ U ⊕ V)) := by
  refine Finset.disjoint_left.2 ?_
  intro x hl hr
  obtain ⟨u, _, rfl⟩ := Finset.mem_map.1 hl
  obtain ⟨v, _, h⟩ := Finset.mem_map.1 hr
  cases h

private theorem inl_inr_cover [DecidableEq (U ⊕ V)] :
    Finset.univ.map (Embedding.inl : U ↪ U ⊕ V) ∪
      Finset.univ.map (Embedding.inr : V ↪ U ⊕ V) = Finset.univ := by
  apply Finset.ext
  intro x
  cases x with
  | inl u => exact iff_of_true (Finset.mem_union_left _ (Finset.mem_map.2 ⟨u, Finset.mem_univ _, rfl⟩)) (Finset.mem_univ _)
  | inr v => exact iff_of_true (Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, Finset.mem_univ _, rfl⟩)) (Finset.mem_univ _)

theorem feedback_pair (f : Network A B (U ⊕ V)) :
    networkFeedback (networkFeedback (innerBody f)) = networkFeedback f := by
  classical
  have inner : networkFeedback (innerBody f) =
      retained Embedding.inl (Finset.univ.map Embedding.inr) f := by
    funext x y
    have h := eliminateStates_reindex (A' := A ⊕ U) (B' := B ⊕ U) Finset.univ Embedding.inr
      (Equiv.sumAssoc A U V) (Equiv.sumAssoc B U V) (fun _ => rfl) (fun _ => rfl) f
    change eliminateStates Finset.univ (innerBody f) (.inl x) (.inl y) = _
    rw [show eliminateStates Finset.univ (innerBody f) = _ from h]
    cases x <;> cases y <;> rfl
  rw [inner]
  exact feedback_partition Embedding.inl _ inl_inr_disjoint inl_inr_cover f

omit [Fintype U] in
private theorem after_retained (f : (A ⊕ U) → (B ⊕ V) → Scalar) (q : V → U → Scalar) :
    retained Embedding.inl (Finset.univ.map Embedding.inr) (slidingNetwork f q) =
      slidingAfter f q := by
  have hz : ∀ i ∈ Finset.univ.map Embedding.inr, ∀ j ∈ Finset.univ.map Embedding.inr,
      slidingNetwork f q (.inr i) (.inr j) = 0 := by
    intro i hi j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hj
    rfl
  funext x y
  unfold retained
  rw [eliminateStates_noInternalEdges _ _ hz]
  cases x <;> cases y <;> simp [slidingNetwork, slidingAfter, Finset.sum_map]

omit [Fintype V] in
private theorem before_retained (f : (A ⊕ U) → (B ⊕ V) → Scalar) (q : V → U → Scalar) :
    retained Embedding.inr (Finset.univ.map Embedding.inl) (slidingNetwork f q) =
      slidingBefore f q := by
  have hz : ∀ i ∈ Finset.univ.map Embedding.inl, ∀ j ∈ Finset.univ.map Embedding.inl,
      slidingNetwork f q (.inr i) (.inr j) = 0 := by
    intro i hi j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hj
    rfl
  funext x y
  unfold retained
  rw [eliminateStates_noInternalEdges _ _ hz]
  cases x <;> cases y <;> simp [slidingNetwork, slidingBefore, Finset.sum_map]

theorem feedback_slide (f : (A ⊕ U) → (B ⊕ V) → Scalar) (q : V → U → Scalar) :
    networkFeedback (slidingAfter f q) = networkFeedback (slidingBefore f q) := by
  classical
  rw [← after_retained, ← before_retained]
  exact (feedback_partition Embedding.inl _ inl_inr_disjoint inl_inr_cover _).trans
    (feedback_partition Embedding.inr _ inl_inr_disjoint.symm
      (by rw [Finset.union_comm]; exact inl_inr_cover) _).symm

end Silmaril.Calco2019.Proofs.CounterSemiringStages
