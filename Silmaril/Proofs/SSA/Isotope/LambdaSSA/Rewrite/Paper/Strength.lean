module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Strength.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Thms

/-! # Iteration with a retained left factor -/

public section

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open CfgEta.TypeCategory (whiskerLeftRegion whiskerLeftBody whiskerLeftRegion_typed seqValueBranches)
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open SyntacticCategory (iterateRegion iterationBody iterationDispatch)
open CfgEta (singleCfg reentry)
open Silmaril.DeBruijn (lift)

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Strength

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B : τ} {p : Region Φ}

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem lift_agree {Γ : VCtx τ} {U : τ} {θ υ : Nat → Tm Φ}
    (h : ∀ ⦃i T⦄, At Γ i T → θ i = υ i) :
    ∀ ⦃i T⦄, At (U :: Γ) i T → Tm.liftSubst θ i = Tm.liftSubst υ i := by
  intro i T hi
  cases i with
  | zero => rfl
  | succ i =>
    have e := h (show At Γ i T from hi)
    change (θ i).rename Nat.succ = (υ i).rename Nat.succ
    rw [e]

private theorem region_subst_eq {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType Γ r L) {θ υ : Nat → Tm Φ}
    (h : ∀ ⦃i U⦄, At Γ i U → θ i = υ i) :
    r.substVars θ = r.substVars υ := by
  induction hr generalizing θ υ with
  | br _ ha => rw [Region.substVars, Region.substVars, Paper.RetainedLet.term_subst_eq ha (fun _ _ hi => h hi)]
  | let₁ ha _ ih => rw [Region.substVars, Region.substVars, Paper.RetainedLet.term_subst_eq ha (fun _ _ hi => h hi), ih (lift_agree h)]
  | let₂ ha _ ih =>
    simp only [Region.substVars, Tm.liftSubstN, Paper.RetainedLet.term_subst_eq ha (fun _ _ hi => h hi), ih (lift_agree (lift_agree h))]
  | case ha _ _ il ir =>
    rw [Region.substVars, Region.substVars, Paper.RetainedLet.term_subst_eq ha (fun _ _ hi => h hi), il (lift_agree h), ir (lift_agree h)]
  | cfg R _ _ ie ib =>
    rw [Region.substVars, Region.substVars, ie h]
    congr 1
    funext i
    exact ib i (lift_agree h)

private theorem singleton_subst {L : LCtx τ} (hp : Region.HasType [A] p L)
    {θ υ : Nat → Tm Φ} (h : θ 0 = υ 0) : p.substVars θ = p.substVars υ := by
  apply region_subst_eq hp
  intro i T hi
  cases i with
  | zero => exact h
  | succ i => simp [At] at hi

private theorem singleton_rename {L : LCtx τ} (hp : Region.HasType [A] p L)
    {ρ υ : Nat → Nat} (h : ρ 0 = υ 0) : p.renameVars ρ = p.renameVars υ := by
  simp only [Region.renameVars_eq_substVars]
  exact singleton_subst hp (congrArg Tm.var h)

private theorem singleton_tail {Γ : VCtx τ} {L : LCtx τ} (hp : ValueBranches [A] p L) :
    ValueBranches (A :: Γ) p L := by
  have h : Ren [A] (A :: Γ) id := by
    intro i T hi
    cases i with
    | zero => exact hi
    | succ i => simp [At] at hi
  simpa only [Region.renameVars_id] using hp.renameVars h

private def retainedDispatcher (retained : Nat) : Region Φ :=
  .case (.var 0) (.br 1 (.pair (.var (retained + 2)) (.var 0))) (.br 0 (.var 0))

private def packedDispatcher (retained : Nat) : Region Φ :=
  .case (.var 0) (.br 1 (.pair (.var (retained + 2)) (.var 0)))
    (.br 0 (.pair (.var (retained + 2)) (.var 0)))

private theorem plainDispatch_typed {Γ : VCtx τ} {i : Nat} (hi : At Γ i X) :
    ValueBranches (Silmaril.coprod B A :: Γ) (retainedDispatcher i : Region Φ)
      [A, Silmaril.product X B] :=
  .case (.var (i := 0) rfl)
    (.br (ℓ := 1) rfl (.pair (.var (i := i + 2) hi) (.var (i := 0) rfl)))
    (.br (ℓ := 0) rfl (.var (i := 0) rfl))

private theorem packDispatch_typed {Γ : VCtx τ} {i : Nat} (hi : At Γ i X) :
    ValueBranches (Silmaril.coprod B A :: Γ) (packedDispatcher i : Region Φ)
      [Silmaril.product X A, Silmaril.product X B] :=
  .case (.var (i := 0) rfl)
    (.br (ℓ := 1) rfl (.pair (.var (i := i + 2) hi) (.var (i := 0) rfl)))
    (.br (ℓ := 0) rfl (.pair (.var (i := i + 2) hi) (.var (i := 0) rfl)))

private def retainedStep (p : Region Φ) : Region Φ :=
  p.lsubst (fun _ => retainedDispatcher 1)

private def packedStep (p : Region Φ) : Region Φ :=
  .let₂ (.var 0) (p.lsubst (fun _ => packedDispatcher 1))

private theorem retainedStep_typed {Γ : VCtx τ}
    (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    ValueBranches (A :: X :: Γ) (retainedStep p) [A, Silmaril.product X B] :=
  (singleton_tail hp).lsubst (fun _ _ hi =>
    (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ plainDispatch_typed (i := 1) rfl)

private theorem packedBody_typed {Γ : VCtx τ}
    (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    ValueBranches (A :: X :: Γ) (p.lsubst (fun _ => packedDispatcher 1))
      [Silmaril.product X A, Silmaril.product X B] :=
  (singleton_tail hp).lsubst (fun _ _ hi =>
    (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ packDispatch_typed (i := 1) rfl)

private theorem packedStep_typed {Γ : VCtx τ}
    (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    ValueBranches (Silmaril.product X A :: Γ) (packedStep p)
      [Silmaril.product X A, Silmaril.product X B] :=
  .let₂ (.var (i := 0) rfl) (packedBody_typed hp)



private theorem unpacked_square {Γ : VCtx τ}
    (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    Paper.Eqv (A :: X :: Γ)
      ((retainedStep p).lsubst (liftLSubstVars
        (CfgEta.Uniformity.localMap (.pair (.var 1) (.var 0)))))
      ((.br 0 (.pair (.var 1) (.var 0)) : Region Φ).lsubst
        (liftLSubstVars (fun _ => packedStep p)))
      [Silmaril.product X A, Silmaril.product X B] := by
  let a := (Tm.pair (.var 1) (.var 0) : Tm Φ)
  let q := Silmaril.product X A
  let σ := Tm.liftSubstN 2 (Tm.replaceNewest a)
  let κ := Tm.consSubst (.var 0) (Tm.singleSubst (.var 1 : Tm Φ))
  let b := p.lsubst (fun _ => packedDispatcher 1)
  have left : (retainedStep p).lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a)) = b := by
    simp only [retainedStep, lsubst_comp]
    rfl
  have right : (.br 0 a : Region Φ).lsubst (liftLSubstVars (fun _ => packedStep p)) =
      (packedStep p).substVars (Tm.replaceNewest a) := by
    simp only [lsubst, liftLSubstVars, substVars_renameVars]
    congr 1
    funext i
    cases i <;> rfl
  rw [left, right]
  have ht : Tm.HasType (A :: X :: Γ) a q := .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  have hσ : Tm.Subst.HasType (q :: X :: Γ) (A :: X :: Γ) (Tm.replaceNewest a) := by
    refine Tm.Subst.HasType.cons ?_ ht
    intro i T hi
    exact .var (show At (A :: X :: Γ) (i + 1) T from hi)
  have hb : Region.HasType (A :: X :: A :: X :: Γ) (b.substVars σ)
      [q, Silmaril.product X B] :=
    (packedBody_typed (X := X) (Γ := q :: X :: Γ) hp).hasType.substVars
      ((hσ.lift X).lift A)
  have hβ := Paper.Eqv.productBeta (ProductBeta.Step.let₂Beta
    (Tm.BranchValue.var (i := 1) (show At (A :: X :: Γ) 1 X from rfl))
    (Tm.BranchValue.var (i := 0) (show At (A :: X :: Γ) 0 A from rfl)) hb)
  change Paper.Eqv (A :: X :: Γ) ((packedStep p).substVars (Tm.replaceNewest a))
    ((b.substVars σ).substVars κ) [q, Silmaril.product X B] at hβ
  have hbsub : (b.substVars σ).substVars κ = b := by
    rw [substVars_comp]
    unfold b
    rw [substVars_lsubst]
    -- The original producer refers to the state at slot zero.
    have ep : p.substVars (fun i => (σ i).subst κ) = p := by
      exact (singleton_subst hp.hasType (θ := fun i => (σ i).subst κ) (υ := Tm.var)
        rfl).trans (substVars_var p)
    rw [ep]
    rfl
  rw [hbsub] at hβ
  exact hβ.symm

private theorem captured_whisker (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    whiskerLeftRegion (iterateRegion A p) =
      .let₂ (.var 0) (feedbackRegion [A] (fun _ => retainedStep p) 0) := by
  let ρ := lift (Nat.succ ∘ Nat.succ)
  let pairOut : Nat → Region Φ := fun _ => .br 0 (.pair (.var 2) (.var 0))
  change Region.let₂ (.var 0) (((iterateRegion A p).renameVars ρ).lsubst pairOut) = _
  congr 1
  simp only [iterateRegion, feedbackRegion, cfgEntryContinuations, List.length_cons, List.length_nil,
    Region.renameVars, lsubst]
  congr 2
  funext j
  simp only [iterationBody, renameVars_lsubst, renameVars_comp, lsubst_comp]
  have h₁ : p.renameVars (lift ρ ∘ lift Nat.succ) = p :=
    (singleton_rename hp.hasType (ρ := lift ρ ∘ lift Nat.succ) (υ := id) rfl).trans
      (renameVars_id p)
  have h₂ : p.renameVars (lift Nat.succ) = p :=
    (singleton_rename hp.hasType (ρ := lift Nat.succ) (υ := id) rfl).trans (renameVars_id p)
  rw [h₁]
  simp only [retainedStep, renameVars_lsubst, h₂]
  rfl

private theorem finish_packed_entry {q : Region Φ} {W : τ}
    (ht : ValueBranches [Silmaril.product X A] q [Silmaril.product X A, W]) :
    Paper.Eqv [Silmaril.product X A]
      (.let₂ (.var 0) ((.br 0 (.pair (.var 1) (.var 0)) : Region Φ).lsubst
        (liftLSubstVars (fun _ => feedbackRegion [Silmaril.product X A] (fun _ => q) 0))))
      (feedbackRegion [Silmaril.product X A] (fun _ => q) 0) [W] := by
  let P := Silmaril.product X A
  let a := (Tm.pair (.var 1) (.var 0) : Tm Φ)
  let b := q.renameVars (lift Nat.succ)
  let entry := (Region.let₂ (.var 0) (.br 0 a) : Region Φ)
  have he : ValueBranches [P] entry [P, W] :=
    .let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl
      (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))
  have hb : ValueBranches [P,P] b [P,W] := ht.renameVars ((Ren.wk [] P).lift P)
  -- Expand the entry into its continuation, then contract the reconstructed pair.
  have hη := Paper.Eqv.cfgEta (CfgEta.Eqv.eta he hb)
  have hentry : Paper.Eqv [P] (singleCfg entry b) (feedbackRegion [P] (fun _ => q) 0) [W] := by
    exact .cfg (fun _ : Fin 1 => P)
      (.productEta (.let₂Eta (i := 0) (ℓ := 0) rfl rfl))
      (fun _ => Paper.Eqv.refl hb.hasType)
  have lhs : entry.lsubst (reentry b) =
      .let₂ (.var 0) ((.br 0 a : Region Φ).lsubst
        (liftLSubstVars (fun _ => feedbackRegion [P] (fun _ => q) 0))) := by
    change Region.let₂ (.var 0) ((.br 0 a : Region Φ).lsubst
      (liftLSubstVars (liftLSubstVars (reentry b)))) = _
    simp only [lsubst, liftLSubstVars, reentry, feedbackRegion, cfgEntryContinuations,
      List.length_cons, List.length_nil, Region.renameVars, Region.substVars]
    congr 4
    funext j
    simp only [b, renameVars_comp, substVars_renameVars]
    apply singleton_subst ht.hasType
    rfl
  rw [← lhs]
  exact hη.symm.trans hentry

private theorem whisker_iterate_normal (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    Paper.Eqv [Silmaril.product X A]
      (whiskerLeftRegion (iterateRegion A p))
      (feedbackRegion [Silmaril.product X A] (fun _ => packedStep p) 0)
      [Silmaril.product X B] := by
  let Q := Silmaril.product X A
  let W := Silmaril.product X B
  have ht : ValueBranches [Q] (packedStep p) [Q,W] := packedStep_typed hp
  have hq : ValueBranches [Q,X,Q] (packedStep p) [Q,W] := singleton_tail ht
  have hs := unpacked_square (X := X) (Γ := [Q]) hp
  have ha : Tm.BranchValue [A,X,Q] (.pair (.var 1) (.var 0) : Tm Φ) Q :=
    .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  -- Change the feedback state from the unpacked payload to the retained pair.
  have h := Paper.feedback_uniform (retainedStep_typed (Γ := [Q]) hp)
    hq.hasType ha hs
  rw [captured_whisker hp]
  exact (Paper.Eqv.let₂ (.var (i := 0) rfl) h).trans (finish_packed_entry ht)



private def routedDistributor : Region Φ :=
  (distributorRegion : Region Φ).lsubst (fun _ => iterationDispatch)

private def packedDistributor : Region Φ :=
  .let₂ (.var 0) (packedDispatcher 0)

private theorem routedDistributor_eq (X A B : τ) :
    Paper.Eqv [Silmaril.product X (Silmaril.coprod B A)]
      (routedDistributor : Region Φ) packedDistributor
      [Silmaril.product X A, Silmaril.product X B] := by
  let P := Silmaril.product X A
  let R := Silmaril.product X B
  let S := Silmaril.coprod B A
  let T := Silmaril.product X S
  have left (Γ : VCtx τ) {a : Tm Φ} (ha : Tm.BranchValue Γ a R) :
      Paper.Eqv Γ
        (.case (.inl a) (.br 1 (.var 0)) (.br 0 (.var 0))) (.br 1 a) [P,R] := by
    have hl : Region.HasType (R :: Γ) (.br 1 (.var 0) : Region Φ) [P,R] := .br rfl (.var (i := 0) rfl)
    have hr : Region.HasType (P :: Γ) (.br 0 (.var 0) : Region Φ) [P,R] := .br rfl (.var (i := 0) rfl)
    exact .cfgEta (.native ((SubstitutionEquiv.base (.caseInl ha.hasType hl hr)).trans (.letValue ha hl)))
  have right (Γ : VCtx τ) {a : Tm Φ} (ha : Tm.BranchValue Γ a P) :
      Paper.Eqv Γ
        (.case (.inr a) (.br 1 (.var 0)) (.br 0 (.var 0))) (.br 0 a) [P,R] := by
    have hl : Region.HasType (R :: Γ) (.br 1 (.var 0) : Region Φ) [P,R] := .br rfl (.var (i := 0) rfl)
    have hr : Region.HasType (P :: Γ) (.br 0 (.var 0) : Region Φ) [P,R] := .br rfl (.var (i := 0) rfl)
    exact .cfgEta (.native ((SubstitutionEquiv.base (.caseInr ha.hasType hl hr)).trans (.letValue ha hr)))
  have hl := left [B,S,X,T] (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))
  have hr := right [A,S,X,T] (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))
  exact .let₂ (.var (i := 0) rfl) (.case (.var (i := 0) rfl) hl hr)

private theorem packedDistributor_typed (X A B : τ) :
    ValueBranches [Silmaril.product X (Silmaril.coprod B A)] (packedDistributor : Region Φ)
      [Silmaril.product X A, Silmaril.product X B] :=
  .let₂ (.var (i := 0) rfl) (.case (.var (i := 0) rfl)
    (.br (ℓ := 1) rfl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))
    (.br (ℓ := 0) rfl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))))

private theorem packedDistributor_pair (X A B : τ) {Γ : VCtx τ} :
    Paper.Eqv (Silmaril.coprod B A :: A :: X :: Γ)
      ((packedDistributor : Region Φ).substVars (Tm.singleSubst (.pair (.var 2) (.var 0))))
      (packedDispatcher 1)
      [Silmaril.product X A, Silmaril.product X B] := by
  let S := Silmaril.coprod B A
  let Γ' := S :: A :: X :: Γ
  have hr : ValueBranches (S :: X :: Γ') (packedDispatcher 0 : Region Φ)
      [Silmaril.product X A, Silmaril.product X B] := packDispatch_typed (i := 0) rfl
  exact .productBeta (.let₂Beta (.var (i := 2) rfl) (.var (i := 0) rfl) hr.hasType)

private theorem packedStep_eq (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    Paper.Eqv [Silmaril.product X A]
      (iterationBody (compLSubst (fun _ => whiskerLeftRegion p) (fun _ => distributorRegion) 0))
      (packedStep p) [Silmaril.product X A, Silmaril.product X B] := by
  let P := Silmaril.product X A
  let R := Silmaril.product X B
  let S := Silmaril.coprod B A
  let T := Silmaril.product X S
  let ρ := lift (Nat.succ ∘ Nat.succ)
  have eq : iterationBody (compLSubst (fun _ => whiskerLeftRegion p) (fun _ => distributorRegion) 0) =
      (whiskerLeftRegion p).lsubst (liftLSubstVars (fun _ => routedDistributor)) := by
    simp only [iterationBody, compLSubst, lsubst_comp, routedDistributor]
    rfl
  rw [eq]
  have e := (routedDistributor_eq (Φ := Φ) X A B).renameVars ((Ren.wk [] P).lift T)
  refine (Paper.lsubst_singleton_congr (whiskerLeftRegion_typed X hp) e).trans ?_
  change Paper.Eqv [P] ((whiskerLeftRegion p).lsubst
    (liftLSubstVars (fun _ => packedDistributor))) (packedStep p) [P,R]
  simp only [whiskerLeftRegion, whiskerLeftBody, lsubst, packedStep]
  apply Paper.Eqv.let₂ (.var (i := 0) rfl)
  have ep : p.renameVars ρ = p :=
    (singleton_rename hp.hasType (ρ := ρ) (υ := id) rfl).trans (renameVars_id p)
  rw [show lift (Nat.succ ∘ Nat.succ) = ρ from rfl, ep, lsubst_comp]
  apply Paper.lsubst_singleton_congr (singleton_tail hp)
  change Paper.Eqv [S,A,X,P]
    (((packedDistributor : Region Φ).renameVars (lift Nat.succ) |>.renameVars (lift Nat.succ)
      |>.renameVars (lift Nat.succ) |>.renameVars (lift Nat.succ)).substVars
        (Tm.singleSubst (.pair (.var 2) (.var 0))))
    (packedDispatcher 1) [P,R]
  have er := singleton_rename (packedDistributor_typed (Φ := Φ) X A B).hasType
    (ρ := lift Nat.succ) (υ := id) rfl
  simp only [renameVars_id] at er
  simp only [er]
  exact packedDistributor_pair X A B



theorem whiskerLeftRegion_iterate (X : τ) (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    Paper.Eqv [Silmaril.product X A]
      (whiskerLeftRegion (iterateRegion A p))
      (iterateRegion (Silmaril.product X A)
        (compLSubst (fun _ => whiskerLeftRegion p) (fun _ => distributorRegion) 0))
      [Silmaril.product X B] := by
  let P := Silmaril.product X A
  let R := Silmaril.product X B
  have e := (packedStep_eq (X := X) hp).renameVars ((Ren.wk [] P).lift P)
  have e' : Paper.Eqv [P]
      (iterateRegion P (compLSubst (fun _ => whiskerLeftRegion p) (fun _ => distributorRegion) 0))
      (feedbackRegion [P] (fun _ => packedStep p) 0) [R] :=
    .cfg (fun _ : Fin 1 => P)
      (.refl (.br (ℓ := 0) rfl (.var (i := 0) rfl))) (fun _ => e)
  exact (whisker_iterate_normal (X := X) hp).trans e'.symm

set_option backward.isDefEq.respectTransparency false in
theorem whiskerLeft_iterateSum (X : τ)
    (f : ofType (Φ := Φ) A ⟶ ofType (Silmaril.coprod B A)) :
    whiskerLeft (τ := τ) (ofType X) (iterateSum f) =
      iterateSum (A := Silmaril.product X A) (B := Silmaril.product X B)
        (whiskerLeft (τ := τ) (ofType X) f ≫ ofRegion (τ := τ) (distributorRegion_typed X B A)) := by
  obtain ⟨p, hp, h⟩ := exists_ofRegion (A := A) (B := Silmaril.coprod B A) f
  rw [h, iterateSum_ofRegion, whiskerLeft_ofRegion, whiskerLeft_ofRegion,
    ofRegion_comp _ _ (seqValueBranches (whiskerLeftRegion_typed X hp) (distributorRegion_typed X B A)),
    iterateSum_ofRegion, ofRegion_eq_iff]
  exact whiskerLeftRegion_iterate X hp



local notation "Comp" => TypeCategory (τ := τ) Φ

set_option backward.isDefEq.respectTransparency false in
theorem whiskerLeft_iterate (Z : Comp) {X Y : Comp} (f : X ⟶ Y ⨿ X) :
    Paper.TypeCategory.iterate (whiskerLeft Z f ≫ leftCoproductDistributor Z Y X) =
      whiskerLeft Z (Paper.TypeCategory.iterate f) := by
  let z : τ := Z
  let x : τ := X
  let y : τ := Y
  let i := sumIso (Φ := Φ) y x
  let o := sumIso (Φ := Φ) (Silmaril.product z y) (Silmaril.product z x)
  change iterateSum (A := Silmaril.product z x) (B := Silmaril.product z y)
    ((whiskerLeft Z f ≫ (whiskerLeft Z i.inv ≫
      ofRegion (τ := τ) (distributorRegion_typed z y x) ≫ o.hom)) ≫ o.inv) =
    whiskerLeft Z (iterateSum (A := x) (B := y) (f ≫ i.inv))
  rw [whiskerLeft_iterateSum]
  simp only [whiskerLeft_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Strength
