module

public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.TypedEquiv
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.Semantics.Agreement
public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.MonadicSoundness
import Silmaril.Proofs.SSA.Isotope.LetIter.CategoricalAgreement

/-! # Denotational soundness for proof-relevant LetIter -/

public section

universe u v w q r

namespace Silmaril.Isotope.LetIter.ProofRelevant.Semantics

open CategoryTheory Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.ProofRelevant.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}

/-- Each typed equation preserves the direct monadic denotation at its specified derivations. -/
theorem sound {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (d : TypedEquiv.Deriv (⊥ : ε) Γ ha hb) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) ha γ ρ = denote (m := m) (ε := ε) hb γ ρ :=
  sound_proof d γ ρ

/-- Merely having a typed equation also suffices for soundness at the same endpoints. -/
theorem related_sound {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (h : TypedEquiv.Related (⊥ : ε) Γ ha hb) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (m := m) (ε := ε) ha γ ρ = denote (m := m) (ε := ε) hb γ ρ :=
  related_sound_proof h γ ρ

/-- The categorical denotation in the associated Kleisli model agrees with the direct semantics. -/
theorem categorical_denote_eq (h : HasType Φ Γ β a A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    (Categorical.denoteOfType (ε := ε) (m := m) h).of (envToCategorical γ ρ) =
      denote (ε := ε) (m := m) h γ ρ :=
  categorical_denote_eq_proof h γ ρ

/-- Typed equations are sound in the categorical semantics specialized to the Kleisli model. -/
theorem categorical_sound_apply {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (h : TypedEquiv.Related (⊥ : ε) Γ ha hb) (γ : CtxDen Γ) (ρ : BoundDen β) :
    (Categorical.denoteOfType (ε := ε) (m := m) ha).of (envToCategorical γ ρ) =
      (Categorical.denoteOfType (ε := ε) (m := m) hb).of (envToCategorical γ ρ) := by
  rw [categorical_denote_eq, categorical_denote_eq, related_sound h]

/-- Typed equations give equal categorical arrows in the associated Kleisli model. -/
theorem categorical_sound {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
    (h : TypedEquiv.Related (⊥ : ε) Γ ha hb) :
    Categorical.denoteOfType (ε := ε) (m := m) ha =
      Categorical.denoteOfType (ε := ε) (m := m) hb := by
  apply Kleisli.hom_ext
  ext input
  obtain ⟨γ, ρ, rfl⟩ := envToCategorical_surjective_proof input
  exact categorical_sound_apply h γ ρ

end Silmaril.Isotope.LetIter.ProofRelevant.Semantics
