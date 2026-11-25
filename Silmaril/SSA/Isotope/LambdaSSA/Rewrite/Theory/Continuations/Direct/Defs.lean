module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # Regions without locally defined blocks -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region

/-- Branches, lets, case splits and empty CFGs require no local iteration. -/
def NoLocalBlocks {Φ : Type*} : Region Φ → Prop
  | .br _ _ => True
  | .let₁ _ body | .let₂ _ body => NoLocalBlocks body
  | .case _ left right => NoLocalBlocks left ∧ NoLocalBlocks right
  | .cfg entry n _ => n = 0 ∧ NoLocalBlocks entry

end Silmaril.Isotope.LambdaSSA.Region

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe v₁ v₂ u₁ u₂ u₃ u₄

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Exact region typing with a value-category denotation at each branch
argument. Let expressions and case scrutinees may have effects. -/
inductive PureBranches : VCtx τ → Region Φ → LCtx τ → Prop where
  | br (h : At L i A) {ha : Tm.HasType Γ a A} {p : ctxObj M Γ ⟶ M.obj A}
      (da : Denotes J M ha (J.map p)) : PureBranches Γ (.br i a) L
  | let₁ (ha : Tm.HasType Γ a A) (hr : PureBranches (A :: Γ) r L) :
      PureBranches Γ (.let₁ a r) L
  | let₂ (ha : Tm.HasType Γ a (Silmaril.product A B)) (hr : PureBranches (B :: A :: Γ) r L) :
      PureBranches Γ (.let₂ a r) L
  | case (ha : Tm.HasType Γ a (Silmaril.coprod A B))
      (hl : PureBranches (A :: Γ) l L) (hr : PureBranches (B :: Γ) r L) :
      PureBranches Γ (.case a l r) L
  | cfg (R : Fin n → τ) (he : PureBranches Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, PureBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
      PureBranches Γ (.cfg entry n blocks) L

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
