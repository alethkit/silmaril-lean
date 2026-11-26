module

public import Silmaril.SSA.Isotope.LetCase.Categorical.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Environment.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetCase.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory PremonoidalCategory
open scoped MonoidalCategory
open LetCase.LocallyNameless
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj envSnocIso envPairHom freeLookup boundVar dropSlot
    envRenameMap envRenameMap_free envRenameMap_bound envRenameMap_snoc envRenameMap_pair
    envRenameMap_underBinder bind_pre_map pair_pre_map case_pre_map bind_case_capture)
open LetIter.ProofRelevant.Semantics.Categorical (duplicate caseWithContext)

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "Env" => envObj M Γ
local notation "bindArrow" => LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

private theorem denote_cast_result {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    {A B : τ} (h : A = B) (d : Derivation Φ Γ β t A) :
    denote J M (h ▸ d) = denote J M d ≫ J.map (eqToHom (congrArg M.obj h)) := by
  cases h
  simp

theorem denote_rename_proof {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A) :
    ∀ {m : Nat} {δ : BoundCtx τ m} (ρ : BoundCtx.Renaming β δ),
      denote J M (d.rename ρ) = J.map (envRenameMap M Γ ρ) ≫ denote J M d := by
  induction d with
  | fv h =>
      intro m δ ρ
      simp only [Derivation.rename, denote, ← J.map_comp, freeLookup, ← Category.assoc,
        envRenameMap_free]
  | @bv n β i =>
      intro m δ ρ
      change denote J M (ρ.typed i ▸ (Derivation.bv (Φ := Φ) (Γ := Γ) (β := δ)
        (ι := ρ.toFun i))) = J.map (envRenameMap M Γ ρ) ≫ J.map (boundVar M i)
      rw [denote_cast_result, denote, ← J.map_comp, ← J.map_comp, envRenameMap_bound]
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
      intro m δ ρ
      simp only [Derivation.rename, denote, ih, Category.assoc]
  | unit =>
      intro m δ ρ
      simp only [denote, Derivation.rename, ← J.map_comp, ← Category.assoc]
      congr 2
      exact isTerminalTensorUnit.hom_ext _ _
  | pair _ _ iha ihb =>
      intro m δ ρ
      simp only [Derivation.rename, denote, iha, ihb, pair_pre_map, Category.assoc]
  | let₁ _ _ iha ihb =>
      intro m δ ρ
      simp only [Derivation.rename, denote, iha, ihb]
      rw [← J.map_comp_assoc, envRenameMap_snoc, J.map_comp_assoc, bind_pre_map]
  | @let₂ _ β _ _ A B _ _ _ iha ihb =>
      intro m δ ρ
      simp only [Derivation.rename, denote, iha, ihb]
      rw [← J.map_comp_assoc (envPairHom M Γ δ A B), envRenameMap_pair,
        J.map_comp_assoc, ← J.map_comp_assoc, MonoidalCategory.id_tensorHom,
        MonoidalCategory.whisker_exchange, J.map_comp_assoc, bind_pre_map]
      rw [MonoidalCategory.id_tensorHom]
  | @case _ β _ _ _ A B _ _ _ _ ihe ihl ihr =>
      intro m δ ρ
      simp only [Derivation.rename, denote, ihe, ihl, ihr, Category.assoc]
      rw [← J.map_comp_assoc (envSnocIso M Γ δ A).hom,
        ← J.map_comp_assoc (envSnocIso M Γ δ B).hom,
        envRenameMap_snoc, envRenameMap_snoc, J.map_comp_assoc, J.map_comp_assoc, case_pre_map]

theorem denote_underBinder_proof {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 1)}
    {X Y A : τ} (d : Derivation Φ Γ (β.snoc Y) t A) :
    J.map (envSnocIso M Γ (β.snoc X) Y).hom ≫ denote J M (d.underBinder (X := X)) =
      J.map (dropSlot M β X ▷ M.obj Y) ≫ J.map (envSnocIso M Γ β Y).hom ≫ denote J M d := by
  rw [Derivation.underBinder, denote_rename_proof, ← J.map_comp_assoc,
    envRenameMap_underBinder, J.map_comp_assoc]

theorem denote_bindLetCase_proof {n : Nat} {β : BoundCtx τ n} {e : Tm ν Φ n}
    {l r k : Tm ν Φ (n + 1)} {A B D E : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (de : Derivation Φ Γ β e (coprod A B))
    (dl : Derivation Φ Γ (β.snoc A) l D) (dr : Derivation Φ Γ (β.snoc B) r D)
    (dk : Derivation Φ Γ (β.snoc D) k E) :
    denote J M (.let₁ (.case de dl dr) dk) =
      denote J M (.case de (.let₁ dl dk.underBinder) (.let₁ dr dk.underBinder)) := by
  let scrutinee := denote J M de ≫ J.map (M.coprodIso A B).hom
  let continuation := J.map (envSnocIso M Γ β D).hom ≫ denote J M dk
  have branch {X : τ} {b : Tm ν Φ (n + 1)} (db : Derivation Φ Γ (β.snoc X) b D) :
      J.map (envSnocIso M Γ β X).hom ≫ denote J M (.let₁ db dk.underBinder) =
        bindArrow J (J.map (envSnocIso M Γ β X).hom ≫ denote J M db)
          (J.map (fst (Env β) (M.obj X) ▷ M.obj D) ≫ continuation) := by
    rw [denote, denote_underBinder_proof]
    change J.map (envSnocIso M Γ β X).hom ≫
      bindArrow J (denote J M db) (J.map (dropSlot M β X ▷ M.obj D) ≫ continuation) = _
    rw [← bind_pre_map, ← J.map_comp_assoc, ← MonoidalCategory.comp_whiskerRight]
    have drop : (envSnocIso M Γ β X).hom ≫ dropSlot M β X = fst (Env β) (M.obj X) := by
      simp [dropSlot]
    rw [drop]
  change bindArrow J (caseWithContext J scrutinee
      (J.map (envSnocIso M Γ β A).hom ≫ denote J M dl)
      (J.map (envSnocIso M Γ β B).hom ≫ denote J M dr)) continuation =
    caseWithContext J scrutinee
      (J.map (envSnocIso M Γ β A).hom ≫ denote J M (.let₁ dl dk.underBinder))
      (J.map (envSnocIso M Γ β B).hom ≫ denote J M (.let₁ dr dk.underBinder))
  rw [bind_case_capture J central, branch dl, branch dr]

end Silmaril.Isotope.LetCase.Semantics.Categorical
