module

public import Silmaril.SSA.RVSDG.LambdaSSA.Region.Defs

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Region Tm)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj labelObj labelInject Denotes RegionDenotes)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind caseWithContext)

universe u v d h c k
variable {Φ : Type v} {r : Region Φ} {t : Tm Φ}

theorem exit_region (t : Tm Φ) : ExitExpression (exitRegion t) t := by
  induction t with
  | let₁ value body _ ih => exact .let₁ value ih
  | case discr left right _ ihl ihr => exact .case discr ihl ihr
  | _ => exact .exit _

theorem exit_expression_iff : exitExpression r = some t ↔ ExitExpression r t := by
  constructor
  · induction r generalizing t with
    | br ℓ body =>
      cases ℓ with
      | zero =>
        intro eq
        cases eq
        exact .exit _
      | succ => intro eq; cases eq
    | let₁ value r ih =>
      cases hr : exitExpression r with
      | none => simp [exitExpression, hr]
      | some t =>
        simp only [exitExpression, hr, Option.map_some, Option.some.injEq]
        rintro rfl
        exact .let₁ value (ih hr)
    | case discr left right ihl ihr =>
      cases hl : exitExpression left <;> cases hr : exitExpression right
      · intro eq; simp [exitExpression, hl, hr] at eq
      · intro eq; simp [exitExpression, hl, hr] at eq
      · intro eq; simp [exitExpression, hl, hr] at eq
      · intro eq
        simp [exitExpression, hl, hr] at eq
        subst t
        exact .case discr (ihl hl) (ihr hr)
    | let₂ => simp [exitExpression]
    | cfg => simp [exitExpression]
  · intro h
    induction h with
    | exit => rfl
    | let₁ _ _ ih => simp [exitExpression, ih]
    | case _ _ _ ihl ihr => simp [exitExpression, ihl, ihr]

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ] {Γ : List τ} {A : τ}

theorem exit_typing (rel : ExitExpression r t) (ht : Tm.HasType Γ t A) :
    Region.HasType Γ r [A] := by
  induction rel generalizing Γ A with
  | exit => exact .br rfl ht
  | let₁ _ _ ih =>
    cases ht with
    | let₁ ha hb => exact .let₁ ha (ih hb)
  | case _ _ _ ihl ihr =>
    cases ht with
    | case he hl hr => exact .case he (ihl hl) (ihr hr)

variable {D : Type d} {C : Type c} [Category.{h} D] [CartesianMonoidalCategory D]
  [HasFiniteCoproducts D] [SymmetricCategory D] [DistributiveTensor D]
  [Category.{k} C] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : D ⥤ C) [StrongElgotFreydCategory J] (M : TypeModel τ D) [InstructionModel J M Φ]

private theorem case_postcomp {R A B Y Z : D} (scrutinee : J.obj R ⟶ J.obj (A ⨿ B))
    (left : J.obj (R ⊗ A) ⟶ J.obj Y) (right : J.obj (R ⊗ B) ⟶ J.obj Y)
    (f : J.obj Y ⟶ J.obj Z) :
    caseWithContext J scrutinee left right ≫ f =
      caseWithContext J scrutinee (left ≫ f) (right ≫ f) := by
  unfold caseWithContext Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  simp only [Category.assoc, coprod.desc_comp]

set_option backward.isDefEq.respectTransparency false in
theorem exit_denotes (rel : ExitExpression r t) {ht : Tm.HasType Γ t A}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} (d : Denotes J M ht f) :
    RegionDenotes J M (exit_typing rel ht)
      (f ≫ J.map (labelInject M (L := [A]) 0 rfl)) := by
  induction rel generalizing Γ A with
  | exit => exact .br d
  | let₁ _ _ ih =>
    cases d with
    | let₁ dv db =>
      unfold Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
      rw [Category.assoc]
      exact .let₁ dv (ih db)
  | case _ _ _ ihl ihr =>
    cases d with
    | case de dl dr =>
      rw [case_postcomp]
      exact .case de (ihl dl) (ihr dr)

variable {sigs : List (Ports (Ty τ))} {extra : Nat}
variable (sel : Categorical.Selectors D) (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))

set_option backward.isDefEq.respectTransparency false in
theorem region_sound
    (agree : ∀ f : Φ, InstructionModel.denote (J := J) (M := M) f = J.map (prim f))
    {g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]} (rel : RegionRelated r g) :
    ∃ f, RegionDenotes J M (exit_typing rel.represents rel.graph.typing) f ∧
      J.map (entryMap M Γ sel prim) ≫ f =
        J.map (g.denote (valueModel M sel prim) ≫
          (ρ_ (M.obj A)).hom ≫ labelInject M (L := [A]) 0 rfl) := by
  obtain ⟨f, den, eq⟩ := rel.graph.sound M sel prim J agree
  refine ⟨_, exit_denotes J M rel.represents den, ?_⟩
  rw [← Category.assoc, eq, ← J.map_comp]
  exact congrArg J.map (Category.assoc _ _ _)

set_option backward.isDefEq.respectTransparency false in
theorem gamma_region_sound
    {g : GammaGraph Φ extra Γ A} (rel : GammaRegionRelated r g) :
    ∃ f, RegionDenotes J M (exit_typing rel.represents rel.graph.typing) f ∧
      J.map (gammaEntryMap M sel prim extra Γ) ≫ f =
        J.map (g.denote (valueModel M sel prim) ≫
          (ρ_ (M.obj A)).hom ≫ labelInject M (L := [A]) 0 rfl) := by
  obtain ⟨f, den, eq⟩ := rel.graph.sound J M sel prim
  refine ⟨_, exit_denotes J M rel.represents den, ?_⟩
  rw [← Category.assoc, ← J.map_comp, eq, ← J.map_comp]
  exact congrArg J.map (Category.assoc _ _ _)

end Silmaril.SSA.RVSDG.LambdaSSA.Proofs
