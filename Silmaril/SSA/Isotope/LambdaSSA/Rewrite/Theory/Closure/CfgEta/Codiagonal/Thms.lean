module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Codiagonal.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Codiagonal

/-! # Denotational soundness of duplicate-feedback collapse

The one-block rule uses the model's contextual codiagonal law with
equality-induced tensor comparisons. The rule is available for use in a
separate presentation. It adds no constructor to CFG η equivalence.

[Companion rule](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/Uniform.lean#L49)
-/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.Codiagonal

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ]

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- Dispatch a literal one-block CFG on the singleton label coproduct.
The collective block arrow restricts to the actual block denotation. -/
theorem denoteSingleCfg {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : Region.HasType Γ e (A :: L)) (hp : Region.HasType (A :: Γ) p (A :: L)) :
    denoteRegion J M (.cfg (fun _ : Fin 1 => A) he (fun _ => hp)) =
      caseWithContext J (denoteRegion J M he ≫ J.map (labelAppendSplit M [A] L))
        (J.map (snd (ctxObj M Γ) (labelObj M L)))
        (contextualLoop J (J.map (ctxObj M Γ ◁ singletonLabelPayload M A) ≫
          denoteRegion J M hp ≫ J.map (labelAppendSplit M [A] L))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Codiagonal.denoteSingleCfg M J he hp

/-- Collapse two feedback frames over the same state under shared tensor comparisons.
The entry and body can be arbitrary exactly typed regions. -/
theorem collapse
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : Region.HasType Γ e (A :: L)) (hp : Region.HasType (A :: Γ) p (A :: A :: L)) :
    denoteRegion J M (nested_typed he hp) = denoteRegion J M (flattened_typed he hp) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Codiagonal.collapse M J shared he hp

variable [FreydCategory.CentralUnit J]

open Region (ValueBranches)

/-- The constructor-value form also admits any common typed outgoing substitution.
Continuation bodies can have effects and contain nested CFGs. -/
theorem collapsePost
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {Γ : VCtx τ} {L K : LCtx τ} {A : τ} {e p : Region Φ} {σ : Nat → Region Φ}
    (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: A :: L))
    (hσ : Region.LSubst.HasType Γ L K σ) :
    denoteRegion J M ((nested_typed he.hasType hp.hasType).lsubst hσ) =
      denoteRegion J M ((flattened_typed he.hasType hp.hasType).lsubst hσ) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Codiagonal.collapsePost M J shared he hp hσ

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.Codiagonal
