module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CategoricalLink

/-! # Categorical sequencing of typed region continuations -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Connecting a typed region to a family of continuations with an outward CFG
denotes sequential binding. The entry produces its payload before the selected
continuation runs, with the captured variables retained. This holds for arbitrary
typed entries and continuation bodies, including empty exit lists and nested CFGs. -/
theorem RegionDenotes.linkExits {Γ : VCtx τ} {L K : LCtx τ}
    {r : Region Φ} {σ : Nat → Region Φ} {hr : Region.HasType Γ r L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (df : RegionDenotes J M hr f)
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (hk : ContinuationDenotes J M σ k) :
    ∃ hs : Region.HasType Γ (r.linkExits L σ) K, RegionDenotes J M hs (bind J f k) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.linkExits_denotes J M df hk

/-- The chosen denotation of the CFG representation of sequencing is the
categorical bind of the chosen entry denotation with the continuation arrow. -/
theorem denoteRegion_linkExits [RegionTypingCoherent (Φ := Φ) J M]
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ (r.linkExits L σ) K)
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (hk : ContinuationDenotes J M σ k) :
    denoteRegion J M hs = bind J (denoteRegion J M hr) k := by
  obtain ⟨_, d⟩ := (denoteRegion_spec J M hr).linkExits J M hk
  exact (RegionDenotes.eq_denote (h := hs) J M d).symm

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
