module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.OrdinarySquare.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn

/-! # Lowered returns and bind-first returns in the unary fusion extension -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open BoundSimulation (boundReturn)
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open RetainedLet (returnOnce returnOnce_typed)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
variable {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} {D : τ} {t : Tm Φ}
variable {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

/-- Recursively lowered returns agree with bind-first returns in any
contextual extension that includes the single forwarding fusion step. -/
theorem returnRegion_eq_returnOnce
    (includeStep : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
    (ht : Tm.HasType Γ t D) :
    Extension.Eqv Seed Γ (returnRegion t) (returnOnce t) [D] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.returnRegion_eq_returnOnce includeStep ht

/-- Identify the two typed arrows in the existing seed-parametric singleton quotient. -/
theorem mapped_returnTerm_eq_boundReturn {A : τ}
    (includeStep : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
    (ht : Tm.HasType [A] t D) :
    (Extension.Singleton.projection Seed).map (returnTerm ht) =
      (Extension.Singleton.projection Seed).map (boundReturn ht) :=
  (Extension.Singleton.ofRegion_eq_iff Seed (returnRegion_typed ht) (returnOnce_typed ht)).2
    (returnRegion_eq_returnOnce includeStep ht)

section Soundness

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind duplicate)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The primitive forwarding fusion has a common arrow at every exact typing. -/
theorem Step.denotes (e : Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.step_denotes J M e hr hs

/-- The full lowering comparison has a common graph arrow by the existing
denotation theorem. Shared tensor comparisons in Paper models supply its
central-diagonal premise. -/
theorem lowering_denotes
    (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (ht : Tm.HasType Γ t D) :
    ∃ f, RegionDenotes J M (returnRegion_typed ht).hasType f ∧
      RegionDenotes J M (returnOnce_valueBranches ht).hasType f :=
  ⟨_, denoteRegion_spec J M _,
    (denote_returnRegion_boundReturn J M copyCentral ht).symm ▸ denoteRegion_spec J M _⟩

end Soundness

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn
