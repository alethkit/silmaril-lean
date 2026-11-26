module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.OrdinarySquare.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Thms

public section

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFold

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold
open Paper.BoundSimulation

universe u v w u₁ u₂ v₁ v₂

section Soundness


variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

variable {Γ : VCtx τ} {L : LCtx τ} {A D : τ}

theorem fold_instruction_free : InstructionFree (foldTerm (Φ := Φ)) := by
  let : HasEff Φ Bool := ⟨fun _ => true⟩
  exact .case .var .var .var

theorem foldStep_valueBranches {r s : Region Φ} (e : FoldStep pe Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases e with
  | @simulate L X entry p q he hp hq square =>
    have maps : LSubst.ValueFamily Γ (Silmaril.coprod X X :: L) (X :: L)
        (boundLocalMap (foldTerm (Φ := Φ))) := by
      intro i Y hi
      cases i with
      | zero =>
        cases Option.some.inj hi
        exact (Region.HasType.br (ℓ := 0) (show At (X :: L) 0 X from rfl) (fold_typed X)).bindBranchArguments
      | succ i => exact .br (ℓ := i + 1) hi (.var (i := 0) rfl)
    exact ⟨.cfg (fun _ : Fin 1 => Silmaril.coprod X X) he (fun _ => hp),
      .cfg (fun _ : Fin 1 => X) (he.lsubst maps) (fun _ => hq)⟩

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem foldStep_denotes
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {r s : Region Φ} (e : FoldStep pe Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  cases e with
  | @simulate L X entry p q he hp hq square =>
    let : HasEff Φ Bool := ⟨fun _ => true⟩
    have noPurePrimitive (f : Φ) : ¬ @IsPure Φ Bool ⟨fun _ => true⟩ false f :=
      Bool.noConfusion
    obtain ⟨_, dt⟩ := (fold_instruction_free (Φ := Φ)).denotes_map J M (fold_typed X)
      (fun f hf => (noPurePrimitive f hf).elim)
    have eq := sound_bound_simulation_of_denotations J M shared he hp hq.hasType dt
      (Paper.WithCaseReturns.Eqv.sound pe J M shared square)
    let hleft := HasType.cfg (fun _ : Fin 1 => Silmaril.coprod X X) he.hasType (fun _ => hp.hasType)
    let hright := HasType.cfg (fun _ : Fin 1 => X)
      (he.hasType.lsubst (boundLocalMap_typed (fold_typed X))) (fun _ => hq.hasType)
    change denoteRegion J M hleft = denoteRegion J M hright at eq
    exact ⟨denoteRegion J M hr, denoteRegion_spec J M hr, eq.symm ▸ denoteRegion_spec J M hs⟩

theorem old_case_returns_included {r s : Region Φ}
    (h : Paper.WithCaseReturns.Eqv pe Γ r s L) :
    Paper.Extension.Eqv (JoinedStep pe) Γ r s L := by
  induction h with
  | paper e => exact .paper e
  | extra hr hs seed => exact .extra hr hs (.inl seed)
  | symm h ih => exact .symm ih
  | trans h k ih ik => exact .trans ih ik
  | let₁ ht h ih => exact .let₁ ht ih
  | let₂ ht h ih => exact .let₂ ht ih
  | case ht h k ih ik => exact .case ht ih ik
  | cfg R h bs ih ib => exact .cfg R ih ib
  | lsubstCongr hr h ih => exact .lsubstCongr hr ih
  | lsubstPost h hr hs typed ih => exact .lsubstPost ih hr hs typed
  | substVars h ht ih => exact .substVars ih ht
  | renameLabels h hρ ih => exact .renameLabels ih hρ

theorem fold_extra_preserves_denotation
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {r s : Region Φ} (eq : Paper.Extension.Eqv (JoinedStep pe) Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  apply Paper.Extension.Eqv.sound J M shared ?_ eq hr hs
  intro Γ r s L seed hr hs
  rcases seed with old | fold
  · have e := Paper.WithCaseReturns.Eqv.sound pe J M shared
      (.extra hr hs old) hr hs
    exact ⟨_, denoteRegion_spec J M hr, e.symm ▸ denoteRegion_spec J M hs⟩
  · exact foldStep_denotes pe J M shared fold hr hs

end Soundness

section Alternating

open Paper.BoundSimulation
open Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
local notation "S" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "X" => ofType (Φ := Φ)
local notation "P" => Paper.TypeCategory (τ := τ) Φ
local infixr:65 " ⊕ₜ " => Silmaril.coprod

private abbrev guard : Region Φ :=
  .case (.var 0) (Paper.RetainedLet.returnOnce (.var 0)) (Paper.RetainedLet.returnOnce (.var 0))

private abbrev identityBranch (A : τ) : ValueBranches [A] (Paper.RetainedLet.returnOnce (.var 0 : Tm Φ)) [A] :=
  Paper.RetainedLet.returnOnce_typed (.var rfl)

private abbrev foldGuarded (A : τ) : ValueBranches [A ⊕ₜ A] (guard (Φ := Φ)) [A] :=
  CfgEta.TypeCategory.caseValueBranches (identityBranch (Φ := Φ) A) (identityBranch A)

private theorem foldGuarded_eq (A : τ) :
    ofRegion (τ := τ) (Φ := Φ) (foldGuarded (Φ := Φ) A) = (sumIso A A).hom ≫ coprod.desc (𝟙 (X A)) (𝟙 (X A)) := by
  have e : ofRegion (τ := τ) (Φ := Φ) (identityBranch (Φ := Φ) A) = 𝟙 (X A) := by
    change returnTerm (show Tm.HasType [A] (.var 0 : Tm Φ) A from .var rfl) = 𝟙 _
    rw [returnTerm_branchValue (.var rfl), ofRegion_id]
  rw [← e]
  exact (coprod_desc_ofRegion (τ := τ) (Φ := Φ) (identityBranch A) (identityBranch A)).symm

private theorem guarded_eq_bound (A : τ) :
    Paper.WithCaseReturns.Eqv pe [A ⊕ₜ A] (guard (Φ := Φ))
      ((Region.br 0 (foldTerm (Φ := Φ))).bindBranchArguments) [A] := by
  have step : Paper.WithCaseReturns.Step (Φ := Φ) pe [A ⊕ₜ A] (Paper.RetainedLet.returnOnce foldTerm) guard [A] :=
    .split (Tm.HasType.var (i := 0) (show At [A] 0 A from rfl))
      (Tm.HasType.var (i := 0) (show At [A] 0 A from rfl)) .var .var
  exact (Paper.Extension.Eqv.extra (Paper.RetainedLet.returnOnce_typed (fold_typed A)).hasType
    (foldGuarded A).hasType (Seed := S) (.inr step)).symm

set_option backward.isDefEq.respectTransparency false

private theorem tagL_fold (A : τ) :
    (sumCofan (Φ := Φ) A A).inl ≫ ofRegion (τ := τ) (Φ := Φ) (foldGuarded A) = 𝟙 (X A) := by
  rw [foldGuarded_eq (Φ := Φ) A, ← Category.assoc (obj := P) (sumCofan (Φ := Φ) A A).inl, sumCofan_inl_sumIso_hom (Φ := Φ) A A, coprod.inl_desc]

private theorem tagR_fold (A : τ) :
    (sumCofan (Φ := Φ) A A).inr ≫ ofRegion (τ := τ) (Φ := Φ) (foldGuarded A) = 𝟙 (X A) := by
  rw [foldGuarded_eq (Φ := Φ) A, ← Category.assoc (obj := P) (sumCofan (Φ := Φ) A A).inr, sumCofan_inr_sumIso_hom (Φ := Φ) A A, coprod.inr_desc]

private theorem alternate_inl {A B : τ} (q : X A ⟶ X B ⨿ X A) :
    (sumCofan (Φ := Φ) A A).inl ≫ alternatingStep q = q ≫ coprod.map (𝟙 _) (sumCofan A A).inr := by
  rw [alternatingStep, ← Category.assoc (obj := P), sumCofan_inl_sumIso_hom (Φ := Φ) A A, coprod.inl_desc]

private theorem alternate_inr {A B : τ} (q : X A ⟶ X B ⨿ X A) :
    (sumCofan (Φ := Φ) A A).inr ≫ alternatingStep q = q ≫ coprod.map (𝟙 _) (sumCofan A A).inl := by
  rw [alternatingStep, ← Category.assoc (obj := P), sumCofan_inr_sumIso_hom (Φ := Φ) A A, coprod.inr_desc]

private theorem alternate_square {A B : τ} (q : X A ⟶ X B ⨿ X A) :
    alternatingStep q ≫ coprod.map (𝟙 _) (ofRegion (foldGuarded (Φ := Φ) A)) =
      ofRegion (foldGuarded (Φ := Φ) A) ≫ q := by
  let f := ofRegion (foldGuarded (Φ := Φ) A)
  let l := (sumCofan (Φ := Φ) A A).inl
  let r := (sumCofan (Φ := Φ) A A).inr
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Φ := Φ) A A)
  · change l ≫ (alternatingStep q ≫ _) = l ≫ (f ≫ q)
    rw [← Category.assoc l, alternate_inl, ← Category.assoc l, tagL_fold A,
      Category.id_comp, Category.assoc, coprod.map_map, Category.id_comp, tagR_fold A,
      coprod.map_id_id, Category.comp_id]
  · change r ≫ (alternatingStep q ≫ _) = r ≫ (f ≫ q)
    rw [← Category.assoc r, alternate_inr, ← Category.assoc r, tagR_fold A,
      Category.id_comp, Category.assoc, coprod.map_map, Category.id_comp, tagL_fold A,
      coprod.map_id_id, Category.comp_id]

variable {A B : τ} {p q : Region Φ}
local notation "T" => (A ⊕ₜ A)

theorem local_square (hp : ValueBranches [T] p [T, B])
    (hq : ValueBranches [A] q [A, B])
    (comm : stepArrow hp = alternatingStep (stepArrow hq)) :
    Paper.WithCaseReturns.Eqv pe [T] (p.lsubst (liftLSubstVars (boundLocalMap foldTerm)))
      ((Region.br 0 foldTerm).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))) [A, B] := by
  let hf := foldGuarded (Φ := Φ) A
  let hb := Paper.RetainedLet.returnOnce_typed (fold_typed (Γ := []) (Φ := Φ) A)
  have ef := guarded_eq_bound (Φ := Φ) pe A
  have hs := (ordinary_square_of_region_iff hp hq hf).1 (comm ▸ alternate_square (stepArrow hq))
  have left : Paper.WithCaseReturns.Eqv pe [T]
      (p.lsubst (liftLSubstVars (boundLocalMap foldTerm)))
      (p.lsubst (liftLSubstVars (regionLocalMap guard))) [A, B] := by
    refine (.lsubstCongr hp ?_)
    intro i E hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      have weak : Ren [A] [A, B] id := by
        intro k D hk
        cases k with
        | zero => exact hk
        | succ k => simp [At] at hk
      simpa only [renameLabels_id, liftLSubstVars, boundLocalMap, regionLocalMap] using ((ef.renameLabels weak).renameVars ((Ren.wk [] T).lift T)).symm
    | succ i =>
      exact .refl (.br (ℓ := i + 1) hi (.var (i := 0) rfl))
  have family : LSubst.ValueFamily ([] : VCtx τ) [A] [A, B] (fun _ => q) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hq
  exact left.trans ((Paper.Extension.Eqv.paper (Seed := S) hs).trans (.lsubstPost ef hf hb (fun _ _ hi => (family.liftVars T hi).hasType)))

end Alternating


section Endpoints

open Paper.BoundSimulation
open Paper.TypeCategory
open Silmaril.DeBruijn (lift)
open Paper.Extension.Singleton (ofRegion_eq_iff projection)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε) {A B : τ}
  {p q : Region Φ}

local notation "E" => JoinedStep (τ := τ) (Φ := Φ) pe
local notation "S" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "T" => Silmaril.coprod A A
local notation "bound" => Paper.RetainedLet.returnOnce (foldTerm (Φ := Φ))

private theorem rename_lift_twice (p : Region Φ) :
    (p.renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ)) =
      (p.renameVars (lift Nat.succ)).renameVars (lift Nat.succ) := by
  rw [renameVars_comp, renameVars_comp]
  congr 1
  funext i
  cases i <;> rfl

private theorem liftFamily (σ : Nat → Region Φ) :
    (fun i => (liftLSubstVars σ i).renameVars (lift (lift Nat.succ))) =
      liftLSubstVars (fun i => (σ i).renameVars (lift Nat.succ)) := by
  funext i
  exact rename_lift_twice (σ i)

private theorem lift_fold :
    (fun i => (boundLocalMap (foldTerm (Φ := Φ)) i).renameVars (lift Nat.succ)) = boundLocalMap foldTerm := by
  funext i
  cases i <;> rfl

private def weakened (r : Region Φ) : Region Φ := r.renameVars (lift Nat.succ)

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem rename_bound : (bound).renameVars (lift Nat.succ) = bound := rfl

private theorem weakened_square
    (sq : Paper.WithCaseReturns.Eqv pe [T]
      (p.lsubst (liftLSubstVars (boundLocalMap foldTerm)))
      ((bound).lsubst (liftLSubstVars (fun _ => q))) [A, B]) :
    Paper.WithCaseReturns.Eqv pe [T, T]
      ((weakened p).lsubst (liftLSubstVars (boundLocalMap foldTerm)))
      ((bound).lsubst (liftLSubstVars (fun _ => weakened q))) [A, B] := by
  simpa only [weakened, renameVars_lsubst, liftFamily, lift_fold, rename_bound] using
    sq.renameVars ((Ren.wk [] T).lift T)

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem fold_entry :
    (Region.br 0 (.var 0 : Tm Φ)).lsubst (boundLocalMap foldTerm) = bound := rfl

private theorem composed_feedback (hq : ValueBranches [A] q [A, B]) :
    Paper.Eqv [T] (.cfg bound 1 (fun _ => weakened q))
      ((bound).lsubst (liftLSubstVars (fun _ => feedbackRegion [A] (fun _ => q) 0))) [B] := by
  let hb : ValueBranches [T] bound [A] := Paper.RetainedLet.returnOnce_typed (fold_typed A)
  have hd : ValueBranches [A,T] (.br 0 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
  have hq' := hq.renameVars ((Ren.wk [] T).lift A)
  have eq := CfgEta.seqCont hb hd hq'
  change CfgEta.Eqv [T] (.cfg ((bound).lsubst (fun _ => .br 0 (.var 0))) 1 (fun _ => weakened q))
    ((bound).lsubst (fun _ => .cfg (.br 0 (.var 0)) 1
      (fun _ => (weakened q).renameVars (lift Nat.succ)))) [B] at eq
  have entry : (bound).lsubst (fun _ => .br 0 (.var 0)) = bound := rfl
  rw [entry] at eq
  have route : (fun _ : Nat => Region.cfg (.br 0 (.var 0)) 1
      (fun _ => (weakened q).renameVars (lift Nat.succ))) =
      liftLSubstVars (fun _ => feedbackRegion [A] (fun _ => q) 0) := by
    funext i
    change Region.cfg (.br 0 (.var 0)) 1 (fun _ => (weakened q).renameVars (lift Nat.succ)) =
      Region.cfg (.br 0 (.var 0)) 1 (fun _ => (weakened q).renameVars (lift (lift Nat.succ)))
    congr 1
    funext j
    exact (rename_lift_twice q).symm
  rw [route] at eq
  exact .cfgEta eq

private theorem iterate_local_square (hp : ValueBranches [T] p [T, B])
    (hq : ValueBranches [A] q [A, B])
    (sq : Paper.WithCaseReturns.Eqv pe [T]
      (p.lsubst (liftLSubstVars (boundLocalMap foldTerm)))
      ((bound).lsubst (liftLSubstVars (fun _ => q))) [A, B]) :
    (projection E).map (Paper.TypeCategory.iterate (stepArrow hp)) =
      (projection E).map (boundReturn (fold_typed A) ≫ Paper.TypeCategory.iterate (stepArrow hq)) := by
  rw [iterate_stepArrow hp, iterate_stepArrow hq]
  let hb : ValueBranches [T] bound [A] := Paper.RetainedLet.returnOnce_typed (fold_typed A)
  let hqLoop := stepFeedback_typed hq
  let fam : LSubst.ValueFamily ([] : VCtx τ) [A] [B] (fun _ => feedbackRegion [A] (fun _ => q) 0) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hqLoop
  let out := hb.lsubst (fam.liftVars T)
  change Paper.Extension.Singleton.ofRegion E (stepFeedback_typed hp) =
    Paper.Extension.Singleton.ofRegion E out
  apply (ofRegion_eq_iff E _ _).2
  have he : ValueBranches [T] (.br 0 (.var 0) : Region Φ) [T, B] := .br rfl (.var rfl)
  have st := FoldStep.simulate (pe := pe) he (hp.renameVars ((Ren.wk [] T).lift T))
      (hq.renameVars ((Ren.wk [] T).lift A)) (weakened_square pe sq)
  obtain ⟨hl, hr⟩ := foldStep_valueBranches pe st
  have hd : Paper.Extension.Eqv E [T] _ _ [B] := .extra hl.hasType hr.hasType (.inr st)
  change Paper.Extension.Eqv E [T]
    (feedbackRegion [T] (fun _ => p) 0)
    (.cfg ((Region.br 0 (.var 0)).lsubst (boundLocalMap foldTerm)) 1 (fun _ => weakened q)) [B] at hd
  rw [fold_entry (Φ := Φ)] at hd
  exact hd.trans (.paper (composed_feedback hq))

end Endpoints


section Alternating

open Paper.TypeCategory
open Paper.BoundSimulation
open Paper.Extension.Singleton (iterateChosen uniformity_of_iso projectStep
  coprodComparison_inv_map iterateChosen_projectStep)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
local notation "E" => JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Q" => Paper.Extension.Singleton.TypeCategory E
local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "F" => Paper.Extension.Singleton.projection E
local notation "X" => ofType (Φ := Φ)
local notation "cmp" => PreservesColimitPair.iso (F)
local infixr:65 " ⊕ₜ " => Silmaril.coprod

set_option backward.isDefEq.respectTransparency false

private noncomputable abbrev stateSum (A : τ) : (F).obj (X A) ⨿ (F).obj (X A) ≅ (F).obj (X (A ⊕ₜ A)) :=
  (cmp (X A) (X A)) ≪≫ ((F).mapIso (sumIso (Φ := Φ) A A)).symm

private theorem stateSum_inl (A : τ) :
    coprod.inl ≫ (stateSum pe A).hom = (F).map (sumCofan A A).inl := by
  change coprod.inl ≫ (cmp (X A) (X A)).hom ≫ (F).map (sumIso A A).inv = _
  rw [PreservesColimitPair.iso_hom, inl_coprodComparison_assoc, ← Functor.map_comp,
    ← sumCofan_inl_sumIso_hom (Φ := Φ) A A, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem stateSum_inr (A : τ) :
    coprod.inr ≫ (stateSum pe A).hom = (F).map (sumCofan A A).inr := by
  change coprod.inr ≫ (cmp (X A) (X A)).hom ≫ (F).map (sumIso A A).inv = _
  rw [PreservesColimitPair.iso_hom, inr_coprodComparison_assoc, ← Functor.map_comp,
    ← sumCofan_inr_sumIso_hom (Φ := Φ) A A, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem transported_fold (A : τ) :
    (stateSum pe A).hom ≫ (F).map (boundReturn (fold_typed (Γ := []) (Φ := Φ) A)) =
      coprod.desc (𝟙 ((F).obj (X A))) (𝟙 ((F).obj (X A))) := by
  have eq := (Paper.Extension.Singleton.ofRegion_eq_iff E (foldGuarded A)
      (Paper.RetainedLet.returnOnce_typed (fold_typed A))).2
    (old_case_returns_included pe (guarded_eq_bound (Φ := Φ) pe A))
  change (F).map (Paper.TypeCategory.ofRegion (foldGuarded A)) =
    (F).map (boundReturn (fold_typed A)) at eq
  rw [← eq]
  apply coprod.hom_ext
  · rw [← Category.assoc, stateSum_inl, ← Functor.map_comp, tagL_fold A, (F).map_id,
      coprod.inl_desc]
  · rw [← Category.assoc, stateSum_inr, ← Functor.map_comp, tagR_fold A, (F).map_id,
      coprod.inr_desc]

private theorem transported_alternate {A B : τ} (q : X A ⟶ X B ⨿ X A) :
    let g := projectStep E q
    let alt := coprod.desc
      (g ≫ coprod.map (𝟙 ((F).obj (X B))) (coprod.inr : (F).obj (X A) ⟶ _))
      (g ≫ coprod.map (𝟙 ((F).obj (X B))) (coprod.inl : (F).obj (X A) ⟶ _))
    (stateSum pe A).hom ≫ projectStep E (alternatingStep q) =
      alt ≫ coprod.map (𝟙 ((F).obj (X B))) (stateSum pe A).hom := by
  dsimp only
  apply coprod.hom_ext
  · rw [← Category.assoc, stateSum_inl, coprod.inl_desc_assoc, Category.assoc, coprod.map_map,
      Category.id_comp, stateSum_inr]
    change (F).map (sumCofan A A).inl ≫ (F).map (alternatingStep q) ≫ (cmp (X B) (X (A ⊕ₜ A))).inv =
      ((F).map q ≫ (cmp (X B) (X A)).inv) ≫ _
    rw [← Functor.map_comp_assoc, alternate_inl, Functor.map_comp, Category.assoc, Category.assoc,
      ← (F).map_id (X B), coprodComparison_inv_map]
    rfl
  · rw [← Category.assoc, stateSum_inr, coprod.inr_desc_assoc, Category.assoc, coprod.map_map,
      Category.id_comp, stateSum_inl]
    change (F).map (sumCofan A A).inr ≫ (F).map (alternatingStep q) ≫ (cmp (X B) (X (A ⊕ₜ A))).inv =
      ((F).map q ≫ (cmp (X B) (X A)).inv) ≫ _
    rw [← Functor.map_comp_assoc, alternate_inr, Functor.map_comp, Category.assoc, Category.assoc,
      ← (F).map_id (X B), coprodComparison_inv_map]
    rfl

theorem double_step {A B : Q} (g : A ⟶ B ⨿ A) :
    iterateChosen E (g ≫ coprod.desc coprod.inl g) = iterateChosen E g := by
  let a : τ := A.as
  let b : τ := B.as
  let q0 := g ≫ (cmp B.as A.as).hom
  obtain ⟨q, hq⟩ := (F).map_surjective q0
  have proj : projectStep E q = g := by
    change (F).map q ≫ (cmp B.as A.as).inv = _
    rw [hq, show q0 = g ≫ (cmp B.as A.as).hom from rfl, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨p, hp, hpEq⟩ := exists_stepArrow (A := a ⊕ₜ a) (B := b) (alternatingStep (A := a) (B := b) q)
  obtain ⟨r, hr, hrEq⟩ := exists_stepArrow (A := a) (B := b) q
  have sq := local_square pe hp hr (hpEq.symm.trans (congrArg (alternatingStep (A := a) (B := b)) hrEq))
  have eq := iterate_local_square pe hp hr sq
  rw [← hpEq, ← hrEq, Functor.map_comp, ← iterateChosen_projectStep E,
    ← iterateChosen_projectStep E] at eq
  let alt : A ⨿ A ⟶ B ⨿ (A ⨿ A) :=
    coprod.desc (g ≫ coprod.map (𝟙 B) coprod.inr) (g ≫ coprod.map (𝟙 B) coprod.inl)
  have comm : alt ≫ coprod.map (𝟙 B) (stateSum pe a).hom =
      (stateSum pe a).hom ≫ projectStep E (alternatingStep q) := by
    have c := transported_alternate pe (A := a) (B := b) q
    dsimp only at c
    rw [proj] at c
    exact c.symm
  have transIso := uniformity_of_iso E (stateSum pe a) alt _ comm
  rw [eq, ← Category.assoc, transported_fold, proj] at transIso
  exact (Paper.WithCaseReturns.StructuralValues.HiddenBit.alternating_fold_iff_double_of_seed E g).1 transIso

end Alternating

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFold
