module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Network.Defs

public section

universe u v w u' v' w'

namespace Silmaril.Calco2019.Proofs.CounterSemiring

open Silmaril.Calco2019.CounterSemiring

variable {A : Type u} {B : Type v} {U : Type w}
  {A' : Type u'} {B' : Type v'} {V : Type w'}

theorem eliminate_reindex (s : Finset V) (e : V ↪ U)
    (row : A' ⊕ V → A ⊕ U) (col : B' ⊕ V → B ⊕ U)
    (hr : ∀ v, row (.inr v) = .inr (e v)) (hc : ∀ v, col (.inr v) = .inr (e v))
    (f : Network A B U) :
    eliminateStates s (fun x y => f (row x) (col y)) =
      fun x y => eliminateStates (s.map e) f (row x) (col y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eliminateStates]; rfl
  | @insert v s hv ih =>
    have hv' : e v ∉ s.map e := fun h => hv (Finset.mem_map.1 h |>.elim
      fun v' ⟨hmem, heq⟩ => e.injective heq ▸ hmem)
    rw [eliminateStates_insert s v hv, Finset.map_insert, eliminateStates_insert _ _ hv']
    rw [ih]
    funext x y
    simp [eliminateState, hr, hc]

theorem eliminate_acyclic (s : Finset U) (f : Network A B U)
    (noEdges : ∀ u ∈ s, ∀ v ∈ s, f (.inr u) (.inr v) = 0)
    (x : A ⊕ U) (y : B ⊕ U) :
    eliminateStates s f x y = f x y + ∑ u ∈ s, f x (.inr u) * f (.inr u) y := by
  classical
  induction s using Finset.induction_on generalizing x y with
  | empty => simp [eliminateStates]; rfl
  | @insert u s hu ih =>
    have hs : ∀ v ∈ s, ∀ w ∈ s, f (.inr v) (.inr w) = 0 :=
      fun v hv w hw => noEdges v (Finset.mem_insert_of_mem hv) w (Finset.mem_insert_of_mem hw)
    have hself := noEdges u (Finset.mem_insert_self _ _) u (Finset.mem_insert_self _ _)
    have hin (z : A ⊕ U) : (∑ v ∈ s, f z (.inr v) * f (.inr v) (.inr u)) = 0 :=
      Finset.sum_eq_zero fun v hv => by
        rw [noEdges v (Finset.mem_insert_of_mem hv) u (Finset.mem_insert_self _ _), mul_zero]
    have hout (z : B ⊕ U) : (∑ v ∈ s, f (.inr u) (.inr v) * f (.inr v) z) = 0 :=
      Finset.sum_eq_zero fun v hv => by
        rw [noEdges u (Finset.mem_insert_self _ _) v (Finset.mem_insert_of_mem hv), zero_mul]
    rw [eliminateStates_insert s u hu]
    simp only [eliminateState, Scalar.eliminate, ih hs, hin, hout, hself, add_zero,
      show Scalar.star 0 = 1 from rfl, mul_one, Finset.sum_insert hu]
    ac_rfl

end Silmaril.Calco2019.Proofs.CounterSemiring
