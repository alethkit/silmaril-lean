module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.LocalLabels.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationLoop
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels

/-! # Categorical continuation fusion for the native CFG dispatcher -/

public section

universe v₁ v₂ u₁ u₂ u₃

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop duplicate extend)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "fst" => CartesianMonoidalCategory.fst
local notation "snd" => CartesianMonoidalCategory.snd

set_option backward.isDefEq.respectTransparency false

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem label_ext {L : LCtx τ} {X : V} {f g : labelObj M L ⟶ X}
    (h : ∀ ⦃i A⦄ (hi : At L i A), labelInject M i hi ≫ f = labelInject M i hi ≫ g) : f = g := by
  apply Limits.Sigma.hom_ext
  intro i
  have eq := h (labelAt_get L i)
  unfold labelInject at eq
  simpa using eq

private theorem liftLocalLabels_split {n : Nat} (R : Fin n → τ)
    {Γ : VCtx τ} {L K : LCtx τ}
    (k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)) :
    liftLocalLabels J M (List.ofFn R) k ≫ J.map (labelAppendSplit M (List.ofFn R) K) =
      J.map (ctxObj M Γ ◁ labelAppendSplit M (List.ofFn R) L) ≫
        liftExit J (B := labelObj M (List.ofFn R)) k := by
  let ρ := outwardLabelRenaming (List.ofFn R) K
  let split := labelAppendSplit M (List.ofFn R) K
  have outward : labelMap M (outwardLabelRenaming (List.ofFn R) K) ≫
      labelAppendSplit M (List.ofFn R) K = coprod.inl := by
    apply label_ext M
    intro i A h
    rw [← Category.assoc, labelInject_labelMap]
    change labelInject M ((List.ofFn R).length + i) (ρ h) ≫ split = _
    simpa only [List.length_ofFn] using labelAppendSplit_exit M R h
  have inside : labelMap M (localLabelRenaming (List.ofFn R) K) ≫
      labelAppendSplit M (List.ofFn R) K = coprod.inr := by
    apply label_ext M
    intro i A h
    have hi : i < n := by
      have := (List.getElem?_eq_some_iff.mp h).1
      simpa only [List.length_ofFn] using this
    let j : Fin n := ⟨i, hi⟩
    have hA := Option.some.inj (h.symm.trans (ofFnAt R j))
    subst A
    rw [← Category.assoc, labelInject_labelMap]
    exact labelAppendSplit_local M R j K
  simp only [liftLocalLabels, liftExit, routeEnvironment, Category.assoc, coprod.desc_comp,
    ← J.map_comp]
  rw [outward, inside]

theorem cfg_bindContinuation [FreydCategory.CentralUnit J] {n : Nat} (R : Fin n → τ)
    {Γ : VCtx τ} {L K : LCtx τ}
    (entry : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L)))
    (body : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ J.obj (labelObj M (List.ofFn R ++ L)))
    (k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K))
    (central : IsCentral (J.map (duplicate (ctxObj M Γ)) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) (ctxObj M Γ) (ctxObj M Γ)).inv))
    (shared : ∃ e : J.obj (ctxObj M Γ) ⊗ J.obj (ctxObj M Γ ⊗ labelObj M (List.ofFn R)) =
      J.obj (ctxObj M Γ ⊗ (ctxObj M Γ ⊗ labelObj M (List.ofFn R))),
      Functor.StrongPremonoidal.tensorIso (J := J) (ctxObj M Γ)
        (ctxObj M Γ ⊗ labelObj M (List.ofFn R)) = eqToIso e) :
    let E := ctxObj M Γ
    let D := labelObj M (List.ofFn R ++ L)
    let F := finiteLabelObj M R
    let s := J.map ((𝟙 E) ⊗ₘ labelObjToFinite M R)
    let liftK := liftLocalLabels J M (List.ofFn R) k
    caseWithContext J (bindArrow J entry liftK ≫ J.map (labelAppendSplit M (List.ofFn R) K))
        (J.map (snd E (labelObj M K)))
        (contextualLoop J (s ≫
          bindArrow J body (J.map (fst E F ▷ D) ≫ liftK) ≫
          J.map (labelAppendSplit M (List.ofFn R) K))) =
      bindArrow J (caseWithContext J (entry ≫ J.map (labelAppendSplit M (List.ofFn R) L))
        (J.map (snd E (labelObj M L)))
        (contextualLoop J (s ≫ body ≫ J.map (labelAppendSplit M (List.ofFn R) L)))) k := by
  dsimp only
  simp only [MonoidalCategory.id_tensorHom]
  let E := ctxObj M Γ
  let A := labelObj M (List.ofFn R)
  let F := finiteLabelObj M R
  let select := E ◁ labelObjToFinite M R
  let split := labelAppendSplit M (List.ofFn R) L
  let split' := labelAppendSplit M (List.ofFn R) K
  let liftK := liftLocalLabels J M (List.ofFn R) k
  let exit := liftExit J (B := A) k
  have liftSplit : liftK ≫ J.map split' = J.map (E ◁ split) ≫ exit :=
    liftLocalLabels_split J M R k
  have entryEq : bindArrow J entry liftK ≫ J.map split' =
      bindArrow J (entry ≫ J.map split) exit := by
    simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc,
      extend_post_map, liftSplit, E]
  have bodyEq : J.map select ≫ bindArrow J body (J.map (fst E F ▷ labelObj M (List.ofFn R ++ L)) ≫ liftK) ≫
      J.map split' =
      retainEnvironment J (fst E A) (J.map select ≫ body ≫ J.map split) ≫ exit := by
    rw [bind_retainEnvironment]
    simp only [Category.assoc, liftSplit]
    rw [retainEnvironment_pre_assoc, show select ≫ fst E F = fst E A from
      CartesianMonoidalCategory.whiskerLeft_fst E _]
    simp only [retainEnvironment_comp, retainLeft_comp, retainLeft_map, Category.assoc, E]
  change caseWithContext J (bindArrow J entry liftK ≫ J.map split')
    (J.map (snd E (labelObj M K))) (contextualLoop J (J.map select ≫
      bindArrow J body (J.map (fst E F ▷ labelObj M (List.ofFn R ++ L)) ≫ liftK) ≫ J.map split')) = _
  rw [entryEq, bodyEq, caseLoop_exitContinuation J central shared]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
