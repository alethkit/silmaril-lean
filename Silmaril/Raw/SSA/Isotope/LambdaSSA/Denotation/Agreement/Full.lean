module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Denotation.Agreement.Region

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

/-! # Agreement of the chosen direct lambda-SSA denotations -/

namespace Silmaril.Isotope.LambdaSSA.Semantics

open CategoryTheory Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (typeJ bind_of pair_of caseWithContext_of comp_map_of contextualLoop_of)

universe u v q r

namespace Agreement

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

noncomputable def TermCoherent : Prop :=
  letI := Categorical.ofMonadicInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.TypingCoherent (Φ := Φ) (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ))

noncomputable def RegionCoherent : Prop :=
  letI := Categorical.ofMonadicInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.RegionTypingCoherent (Φ := Φ) (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ))

/-- The chosen categorical term denotation, specialized directly to the
Kleisli model induced by the monadic interpretation. -/
noncomputable def categoricalTermDenote {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) :=
  letI := Categorical.ofMonadicInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.denote (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) h

/-- The chosen categorical region denotation, including recursive CFG
iteration, specialized directly to the Kleisli model. -/
noncomputable def categoricalRegionDenote {Γ : VCtx τ} {region : Region Φ}
    {L : LCtx τ} (h : Region.HasType Γ region L) :=
  letI := Categorical.ofMonadicInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.denoteRegion (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) h

end Agreement
end Silmaril.Isotope.LambdaSSA.Semantics
