module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Categorical.Defs
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.Semantics.Agreement.Combinators

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

universe u v

/-- Values for a newest-first SSA context, represented in oldest-to-newest
nested-pair order to match the categorical context object. -/
def Env {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] :
    VCtx τ → Type v
  | [] => PUnit
  | A :: Γ => Env Γ × TyDen A

/-- Interpret a typed SSA variable lookup. -/
def Env.get {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] :
    {Γ : VCtx τ} → Env Γ → (i : Nat) → {A : τ} → At Γ i A → TyDen A
  | [], _, _, _, h => by simp [At] at h
  | B :: Γ, ρ, 0, A, h => by
      have e : B = A := by simpa [At] using h
      exact e ▸ ρ.2
  | _ :: _, ρ, i + 1, _, h => Env.get ρ.1 i h

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]

/-- The exact categorical model underlying a set-valued subtyping model. -/
@[reducible] noncomputable def ofMonadicTypeModel :
    Silmaril.Isotope.LetIter.Semantics.Categorical.TypeModel τ (Type v) :=
  LambdaSSA.Subtyping.Semantics.Categorical.exactTypeModel
    (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.ofTypeModel (τ := τ))

variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [InstructionModel Φ τ ε m]

/-- Read each typed monadic instruction as a Kleisli arrow in the exact model. -/
@[reducible] def ofMonadicInstructionModel :
    Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel
      (Kleisli.Adjunction.toKleisli (ofTypeMonad m)) (ofMonadicTypeModel (τ := τ)) Φ where
  denote f := Kleisli.Hom.mk (TypeCat.ofHom (InstructionModel.denote (m := m) ε f))

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
