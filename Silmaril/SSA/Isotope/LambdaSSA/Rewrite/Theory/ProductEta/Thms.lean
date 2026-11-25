module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductEta

/-! # Categorical validity of product η

Figure 16 of *The Denotational Semantics of SSA* (arXiv:2411.09347v2)
states `let (x, y) = e; (x, y) ≈ e` for arbitrary exactly typed scrutinees.
The region form compares unpacking and branching on the rebuilt pair with
branching directly. The region rules derive this form from expression η
and binding. These theorems concern the categorical denotation.
-/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

local notation "U" => Functor.StrongPremonoidal.unitIso (J := J)

section Terms
variable [DistributiveFreydCategory J]

/-- Unpacking and rebuilding a product preserves the scrutinee's structural arrow. -/
theorem Denotes.let₂_eta (hu : IsCentral (U).hom) {Γ : VCtx τ} {a : Tm Φ} {A B : τ}
    {ha : Tm.HasType Γ a (Silmaril.product A B)}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B))} (da : Denotes J M ha f) :
    Denotes J M (.let₂ ha (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))) f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductEta.term_eta J M hu da

/-- The paper's product η equation for the chosen expression arrows. -/
theorem denote_let₂_eta [TypingCoherent (Φ := Φ) J M] (hu : IsCentral (U).hom)
    {Γ : VCtx τ} {a : Tm Φ} {A B : τ} (ha : Tm.HasType Γ a (Silmaril.product A B)) :
    denote J M (.let₂ ha (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))) = denote J M ha :=
  ((denote_spec J M ha).let₂_eta J M hu).eq_denote J M |>.symm

end Terms

section Regions
variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- Unpacking and rebuilding a product before a branch gives the same
structural arrow as branching directly on the scrutinee. -/
theorem RegionDenotes.let₂_br_eta (hu : IsCentral (U).hom) {Γ : VCtx τ} {a : Tm Φ}
    {A B : τ} {L : LCtx τ} {i : Nat} {ha : Tm.HasType Γ a (Silmaril.product A B)}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B))}
    (hi : At L i (Silmaril.product A B)) (da : Denotes J M ha f) :
    RegionDenotes J M (.let₂ ha (.br hi (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))
      (f ≫ J.map (labelInject M i hi)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductEta.branch_eta J M hu hi da

/-- The region product η equation for the chosen arrows. -/
theorem denoteRegion_let₂_br_eta [RegionTypingCoherent (Φ := Φ) J M]
    (hu : IsCentral (U).hom) {Γ : VCtx τ} {a : Tm Φ} {A B : τ} {L : LCtx τ} {i : Nat}
    (hi : At L i (Silmaril.product A B)) (ha : Tm.HasType Γ a (Silmaril.product A B)) :
    denoteRegion J M (.let₂ ha (.br hi (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))) =
      denoteRegion J M (.br hi ha) := by
  have da := denote_spec J M ha
  exact ((RegionDenotes.let₂_br_eta J M hu hi da).eq_denote J M).symm.trans
    ((RegionDenotes.br (h := hi) da).eq_denote J M)

/-- For a scrutinee already denoted by a value map, product η for branches
holds without a premise on the unit comparison. -/
theorem RegionDenotes.let₂_br_eta_of_map {Γ : VCtx τ} {a : Tm Φ} {A B : τ} {L : LCtx τ}
    {i : Nat} {ha : Tm.HasType Γ a (Silmaril.product A B)}
    {p : ctxObj M Γ ⟶ M.obj (Silmaril.product A B)} (hi : At L i (Silmaril.product A B))
    (da : Denotes J M ha (J.map p)) :
    RegionDenotes J M (.let₂ ha (.br hi (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))
      (J.map p ≫ J.map (labelInject M i hi)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductEta.branch_eta_of_map J M hi da

end Regions

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
