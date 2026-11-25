module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Sequencing.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Sequencing.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgCase.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Soundness.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Composition.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

/-! # Fixpoint for linked LambdaSSA iteration -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Region
open SyntacticCategory (iterationDispatch iterationDispatch_valueBranches)
open Silmaril.Isotope.SSA (Ren)
open Silmaril.DeBruijn (lift)

section Syntax

variable {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]
  {Γ : VCtx τ} {A B : τ} {p : Region Φ}

private theorem singletonFamily {P : τ} {Δ : VCtx τ} {L : LCtx τ} {next : Region Φ}
    (h : HasType (P :: Δ) next L) : LSubst.HasType Δ [P] L (fun _ => next) := by
  intro i T hi
  have eq : T = P := List.mem_singleton.mp (List.mem_of_getElem? hi)
  cases eq
  exact h

private theorem linkedBody_hasType (hp : HasType (A :: Γ) p [Silmaril.coprod B A]) :
    HasType (A :: Γ) (linkedIterationBody A B p) [A, B] :=
  hp.linkExits (singletonFamily (iterationDispatch_valueBranches A B).hasType)

private theorem capturedBlock (hp : HasType (A :: Γ) p [Silmaril.coprod B A]) :
    HasType (A :: A :: Γ) ((linkedIterationBody A B p).renameVars (lift Nat.succ)) [A, B] :=
  (linkedBody_hasType hp).renameVars ((Ren.wk Γ A).lift A)

theorem linkedIterate_hasType (hp : HasType (A :: Γ) p [Silmaril.coprod B A]) :
    HasType (A :: Γ) (linkedIterate A B p) [B] :=
  .cfg (fun _ : Fin 1 => A) (.br (ℓ := 0) rfl (.var (i := 0) rfl))
    (fun _ => capturedBlock hp)

private theorem linked_unfold (hp : HasType (A :: Γ) p [Silmaril.coprod B A]) :
    SubstitutionEquiv (A :: Γ) (linkedIterate A B p)
      (.cfg (linkedIterationBody A B p) 1 (fun _ => (linkedIterationBody A B p).renameVars (lift Nat.succ))) [B] := by
  let R : Fin 1 → τ := fun _ => A
  have hblock := capturedBlock hp
  have harg : Tm.BranchValue (A :: Γ) (.var 0 : Tm Φ) A := .var (i := 0) rfl
  have cancel : ((linkedIterationBody A B p).renameVars (lift Nat.succ)).substVars (Tm.singleSubst (.var 0)) =
      linkedIterationBody A B p :=
    congrFun (compLSubst_id_left (fun _ => linkedIterationBody A B p)) 0
  have hβ := SubstitutionEquiv.letValue harg hblock
  rw [cancel] at hβ
  exact (SubstitutionEquiv.base (.entry (.cfgBrLocal R 0 harg (fun _ => hblock)))).trans
    (.cfg R hβ (fun _ => .base (.refl hblock)))

private theorem decoder_after_cfg (hp : HasType (A :: Γ) p [Silmaril.coprod B A]) :
    SubstitutionEquiv (Silmaril.coprod B A :: A :: Γ)
      (cfgContinuations (fun _ : Fin 1 => (linkedIterationBody A B p).renameVars (lift Nat.succ))
        (fun _ => iterationDispatch) 0)
      (.case (.var 0) (.br 0 (.var 0))
        ((linkedIterate A B p).renameVars (lift (Nat.succ ∘ Nat.succ)))) [B] := by
  let S := Silmaril.coprod B A
  let R : Fin 1 → τ := fun _ => A
  let b := (linkedIterationBody A B p).renameVars (lift Nat.succ)
  let c := b.renameVars (lift Nat.succ)
  have hc : HasType (A :: S :: A :: Γ) c [A, B] :=
    (capturedBlock hp).renameVars ((Ren.wk (A :: Γ) S).lift A)
  have hl : HasType (B :: S :: A :: Γ) (.br 1 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
  have hr : HasType (A :: S :: A :: Γ) (.br 0 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
  have hstep := SubstitutionEquiv.cfg_caseValue R (.var (i := 0) (A := S) rfl) hl hr (fun _ => hc)
  have hreturn := SubstitutionEquiv.base (.entry (.cfgBrExit R (ℓ := 0) rfl
    (.var (i := 0) rfl) (fun _ => hc.renameVars ((Ren.wk (S :: A :: Γ) B).lift A))))
  have hrepeat : (linkedIterate A B p).renameVars (lift (Nat.succ ∘ Nat.succ)) =
      .cfg (.br 0 (.var 0)) 1 (fun _ => c.renameVars (lift Nat.succ)) := by
    simp only [linkedIterate, feedbackRegion, cfgEntryContinuations, List.length_cons, List.length_nil,
      renameVars, Tm.rename, c, b, renameVars_comp]
    congr 1
    funext i
    congr 1
    funext j
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  rw [hrepeat]
  exact hstep.trans (.case (.var rfl) hreturn
    (.base (.refl (.cfg R hr (fun _ => hc.renameVars ((Ren.wk (S :: A :: Γ) A).lift A))))))

theorem linkedFixpointRhs_hasType (hp : HasType (A :: Γ) p [Silmaril.coprod B A]) :
    HasType (A :: Γ) (linkedFixpointRhs A B p) [B] :=
  hp.linkExits (singletonFamily (decoder_after_cfg hp).typed.2)

end Syntax

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext splitMapCoprod extend)
open CategoryTheory.CartesianMonoidalCategory (snd)

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
  [RegionTypingCoherent (Φ := Φ) J M]

omit [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J] in
private theorem case_payload_map [DistributiveFreydCategory J] {E A B X : V}
    (scrutinee : E ⟶ A ⨿ B) (left : A ⟶ X) (right : B ⟶ X) :
    caseWithContext J (J.map scrutinee)
      (J.map (snd E A ≫ left)) (J.map (snd E B ≫ right)) =
        J.map (scrutinee ≫ coprod.desc left right) := by
  let left' := snd E A ≫ left
  let right' := snd E B ≫ right
  have split : splitMapCoprod J (E ⊗ A) (E ⊗ B) ≫ coprod.desc (J.map left') (J.map right') =
      J.map (coprod.desc left' right') := by
    let comparison := coprodComparison J (E ⊗ A) (E ⊗ B)
    apply (cancel_epi comparison).1
    simp only [comparison, splitMapCoprod, IsIso.hom_inv_id_assoc]
    apply coprod.hom_ext
    · simp only [coprodComparison, coprod.inl_desc_assoc, ← J.map_comp, coprod.inl_desc]
    · simp only [coprodComparison, coprod.inr_desc_assoc, ← J.map_comp, coprod.inr_desc]
  have route : (DistributiveTensor.leftIso E A B).inv ≫ coprod.desc left' right' =
      snd E (A ⨿ B) ≫ coprod.desc left right := by
    apply (cancel_epi (DistributiveTensor.leftIso E A B).hom).1
    simp only [Iso.hom_inv_id_assoc]
    apply coprod.hom_ext
    · simp [DistributiveTensor.leftIso, left', CartesianMonoidalCategory.whiskerLeft_snd_assoc]
    · simp [DistributiveTensor.leftIso, right', CartesianMonoidalCategory.whiskerLeft_snd_assoc]
  change extend J (J.map scrutinee) ≫ J.map (DistributiveTensor.leftIso E A B).inv ≫
    splitMapCoprod J (E ⊗ A) (E ⊗ B) ≫ coprod.desc (J.map left') (J.map right') = _
  rw [extend_map, split, ← J.map_comp, route, ← J.map_comp,
    CartesianMonoidalCategory.lift_snd_assoc]

omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M] in
set_option backward.isDefEq.respectTransparency false in
private theorem iterationDispatch_router (Γ : VCtx τ) (A B : τ) :
    ∃ q : labelObj M [Silmaril.coprod B A] ⟶ labelObj M [A, B],
      ContinuationDenotes J M (Φ := Φ) (fun _ => iterationDispatch)
        (J.map (snd (ctxObj M Γ) (labelObj M [Silmaril.coprod B A]) ≫ q)) := by
  let S := Silmaril.coprod B A
  let l := labelInject M (L := [A, B]) 1 (A := B) rfl
  let r := labelInject M (L := [A, B]) 0 (A := A) rfl
  let route := (M.coprodIso B A).hom ≫ coprod.desc l r
  let fromSingleton : labelObj M [S] ⟶ M.obj S :=
    Sigma.desc (fun i => eqToHom (congrArg M.obj (by
      obtain rfl := Fin.eq_zero i
      rfl)))
  let q := fromSingleton ≫ route
  refine ⟨q, ?_⟩
  intro i T hi
  have hT : T = S := List.mem_singleton.mp (List.mem_of_getElem? hi)
  subst T
  have h0 : i = 0 := by have := (List.getElem?_eq_some_iff.mp hi).1; simp at this; omega
  subst i
  have hiq : labelInject M 0 hi ≫ q = route := by
    simp [q, fromSingleton, labelInject]
    rw [Sigma.ι_comp_desc_assoc]
    exact Category.id_comp route
  let h := (iterationDispatch_valueBranches (Φ := Φ) (Γ := Γ) A B).hasType
  have dd := RegionDenotes.case (J := J) (M := M)
    (Denotes.var (Φ := Φ) (Γ := S :: Γ) (i := 0) (A := S) rfl)
    (RegionDenotes.br (h := (show At [A, B] 1 B from rfl))
      (Denotes.var (i := 0) (Γ := B :: S :: Γ) rfl))
    (RegionDenotes.br (h := (show At [A, B] 0 A from rfl))
      (Denotes.var (i := 0) (Γ := A :: S :: Γ) rfl))
  simp only [lookup, ← J.map_comp] at dd
  rw [case_payload_map] at dd
  refine ⟨h, ?_⟩
  simp only [MonoidalCategory.id_tensorHom, ← J.map_comp, ← Category.assoc]
  rw [CartesianMonoidalCategory.whiskerLeft_snd, Category.assoc, hiq]
  simpa only [route, l, r, Category.assoc] using dd

set_option backward.isDefEq.respectTransparency false in
theorem denote_linked_fixpoint {Γ : VCtx τ} {A B : τ} {p : Region Φ}
    (hp : HasType (A :: Γ) p [Silmaril.coprod B A])
    (hi : HasType (A :: Γ) (linkedIterate A B p) [B])
    (hr : HasType (A :: Γ) (linkedFixpointRhs A B p) [B]) :
    denoteRegion J M hi = denoteRegion J M hr := by
  let R : Fin 1 → τ := fun _ => A
  have hu := FreydCategory.CentralUnit.unit_central (J := J)
  have he := linkedBody_hasType hp
  have hb := capturedBlock hp
  have d := decoder_after_cfg hp
  have eq := (SubstitutionEquiv.base (.refl hp)).linkExits (fun _ _ h => by
    have ht := List.mem_singleton.mp (List.mem_of_getElem? h)
    cases ht
    exact d)
  obtain ⟨q, dq⟩ := iterationDispatch_router (Φ := Φ) J M (A :: Γ) A B
  exact ((linked_unfold hp).sound J M hu hi (.cfg R he (fun _ => hb))).trans
    ((denoteRegion_linkedCfgSequencing J M R hp he (fun _ => hb) q dq eq.typed.1).trans
      (eq.sound J M hu eq.typed.1 hr))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
