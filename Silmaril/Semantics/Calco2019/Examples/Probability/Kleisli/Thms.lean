module

public import Silmaril.Semantics.Calco2019.Examples.Probability.Thms
public import Silmaril.Semantics.Calco2019.CompleteElgot.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.ProbabilityKleisli

/-! # The CALCO guard and no-iteration result for Mathlib's PMF monad -/

public section

namespace Silmaril.Calco2019.Examples.Probability

universe u

open CategoryTheory

/-- Example 10(3)'s guard satisfies the three axioms of CALCO Definition 6. -/
noncomputable def pmfGuard : MonadGuardedness typeCoproducts.{u} (ofTypeMonad PMF) :=
  KleisliProofs.pmfGuard

theorem pmf_guarded_iff {A B C : Type u} (f : A → PMF (B ⊕ C)) :
    pmfGuard.guarded (computation PMF f) ↔ Guarded f :=
  KleisliProofs.guarded_iff f

/-- The proposed probability model with this guard cannot satisfy CALCO Definition 19(2). -/
theorem no_conway_uniform (I : pmfGuard.{0}.Conway)
    (hu : I.toFixpoints.Uniform (Kleisli.Adjunction.toKleisli (ofTypeMonad PMF))) : False :=
  KleisliProofs.no_conway_uniform I hu

end Silmaril.Calco2019.Examples.Probability
