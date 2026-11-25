module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Boundary.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.CounterSemiringBoundary

/-! # Boundary changes and disconnected entries under elimination -/

public section

universe u v w u' v'

namespace Silmaril.Calco2019.CounterSemiring

variable {A : Type u} {B : Type v} {U : Type w} {A' : Type u'} {B' : Type v'}

theorem eliminateStates_preBoundary [Fintype A] (a : A' → A → Scalar) (s : Finset U)
    (f : Network A B U) :
    eliminateStates s (preBoundary a f) = preBoundary a (eliminateStates s f) :=
  Proofs.CounterSemiringBoundary.pre_eliminate a s f

theorem eliminateStates_postBoundary [Fintype B] (b : B → B' → Scalar) (s : Finset U)
    (f : Network A B U) :
    eliminateStates s (postBoundary b f) = postBoundary b (eliminateStates s f) :=
  Proofs.CounterSemiringBoundary.post_eliminate b s f

theorem eliminateStates_isolatedInput (s : Finset U) (f : Network A B U) (x : A ⊕ U)
    (h : ∀ u ∈ s, f x (.inr u) = 0) (y : B ⊕ U) : eliminateStates s f x y = f x y :=
  Proofs.CounterSemiringBoundary.isolated_input s f x h y

theorem eliminateStates_isolatedOutput (s : Finset U) (f : Network A B U) (y : B ⊕ U)
    (h : ∀ u ∈ s, f (.inr u) y = 0) (x : A ⊕ U) : eliminateStates s f x y = f x y :=
  Proofs.CounterSemiringBoundary.isolated_output s f y h x

end Silmaril.Calco2019.CounterSemiring
