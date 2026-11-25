module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Boundary.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

public section

universe u v w u' v'

namespace Silmaril.Calco2019.Proofs.CounterSemiringBoundary

open Silmaril.Calco2019.CounterSemiring

variable {A : Type u} {B : Type v} {U : Type w} {A' : Type u'} {B' : Type v'}

private theorem pre_step [Fintype A] (a : A' → A → Scalar) (u : U) (f : Network A B U) :
    eliminateState u (preBoundary a f) = preBoundary a (eliminateState u f) := by
  funext x y
  cases x with
  | inr u => rfl
  | inl x =>
    simp only [eliminateState, preBoundary, Scalar.eliminate, mul_add, Finset.sum_add_distrib]
    simp only [Finset.sum_mul, mul_assoc]

private theorem post_step [Fintype B] (b : B → B' → Scalar) (u : U) (f : Network A B U) :
    eliminateState u (postBoundary b f) = postBoundary b (eliminateState u f) := by
  funext x y
  cases y with
  | inr u => rfl
  | inl y =>
    simp only [eliminateState, postBoundary, Scalar.eliminate, add_mul, Finset.sum_add_distrib]
    simp only [Finset.mul_sum, mul_assoc]

theorem pre_eliminate [Fintype A] (a : A' → A → Scalar) (s : Finset U) (f : Network A B U) :
    eliminateStates s (preBoundary a f) = preBoundary a (eliminateStates s f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eliminateStates]; rfl
  | @insert u s hu ih => rw [eliminateStates_insert _ _ hu, ih, pre_step, eliminateStates_insert _ _ hu]

theorem post_eliminate [Fintype B] (b : B → B' → Scalar) (s : Finset U) (f : Network A B U) :
    eliminateStates s (postBoundary b f) = postBoundary b (eliminateStates s f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eliminateStates]; rfl
  | @insert u s hu ih => rw [eliminateStates_insert _ _ hu, ih, post_step, eliminateStates_insert _ _ hu]

theorem isolated_input (s : Finset U) (f : Network A B U) (x : A ⊕ U)
    (h : ∀ u ∈ s, f x (.inr u) = 0) (y : B ⊕ U) :
    eliminateStates s f x y = f x y := by
  classical
  induction s using Finset.induction_on generalizing y with
  | empty => simp [eliminateStates]; rfl
  | @insert u s hu ih =>
    have hs := fun v hv => h v (Finset.mem_insert_of_mem hv)
    rw [eliminateStates_insert _ _ hu]
    simp only [eliminateState, Scalar.eliminate, ih hs, h u (Finset.mem_insert_self _ _),
      zero_mul, add_zero]

theorem isolated_output (s : Finset U) (f : Network A B U) (y : B ⊕ U)
    (h : ∀ u ∈ s, f (.inr u) y = 0) (x : A ⊕ U) :
    eliminateStates s f x y = f x y := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => simp [eliminateStates]; rfl
  | @insert u s hu ih =>
    have hs := fun v hv => h v (Finset.mem_insert_of_mem hv)
    rw [eliminateStates_insert _ _ hu]
    simp only [eliminateState, Scalar.eliminate, ih hs, h u (Finset.mem_insert_self _ _),
      mul_zero, add_zero]

end Silmaril.Calco2019.Proofs.CounterSemiringBoundary
