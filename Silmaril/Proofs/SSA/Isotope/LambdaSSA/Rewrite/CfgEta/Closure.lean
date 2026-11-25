module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Composition.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheoryTyping
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheorySubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies
import Silmaril.Raw.SSA.Isotope.LambdaSSA.ContinuationLaws

/-! # Substitution closure and fixpoint for one-block literal CFG η -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

open Silmaril.Isotope.LambdaSSA
open Region Region.CfgEta
open Silmaril.Isotope.SSA (Ren)
open Silmaril.DeBruijn (lift)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
  (valuesTyped liftValues branchValue_subst valueBranches_lsubst valueFamily_liftVars)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem eta {Γ : VCtx τ} {L : LCtx τ} {A : τ} {entry block : Region Φ}
    (he : ValueBranches Γ entry (A :: L)) (hb : ValueBranches (A :: Γ) block (A :: L)) :
    Eqv Γ (singleCfg entry block) (entry.lsubst (reentry block)) L := by
  simpa only [lsubst_labelId] using Eqv.etaPost he hb (LSubst.HasType.id Γ L)

private theorem liftLabels {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (h : LSubst.HasType Γ L K σ) {n : Nat} (R : Fin n → τ) :
    LSubst.HasType Γ (List.ofFn R ++ L) (List.ofFn R ++ K) (liftLSubstN n σ) := by
  simpa only [List.length_ofFn] using h.append (List.ofFn R)

theorem eqv_lsubst {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) :
    Eqv Γ (r.lsubst σ) (s.lsubst σ) K := by
  induction h generalizing K σ with
  | native h => exact .native (h.lsubst hσ)
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hσ) (ih₂ hσ)
  | let₁ ha _ ih => exact .let₁ ha (ih (hσ.liftVars _))
  | let₂ ha _ ih => exact .let₂ ha (ih ((hσ.liftVars _).liftVars _))
  | case ha _ _ ihl ihr => exact .case ha (ihl (hσ.liftVars _)) (ihr (hσ.liftVars _))
  | cfg R _ _ ihe ihb =>
    exact .cfg R (ihe (liftLabels hσ R)) (fun i => ihb i ((liftLabels hσ R).liftVars _))
  | etaPost he hb hυ =>
    simpa only [lsubst_comp, compLSubst_assoc] using Eqv.etaPost he hb (hυ.comp hσ)

theorem eqv_renameLabels {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {ρ : Nat → Nat} (hρ : Ren L K ρ) :
    Eqv Γ (r.renameLabels ρ) (s.renameLabels ρ) K := by
  rw [renameLabels_eq_lsubst, renameLabels_eq_lsubst]
  exact eqv_lsubst h (fun _ _ hi => .br (hρ hi) (.var rfl))

private theorem valueSubst {Γ Δ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {θ : Nat → Tm Φ}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    ValueBranches Δ (r.substVars θ) L := by
  induction hr generalizing Δ θ with
  | br h ha => exact .br h (branchValue_subst ha hθ)
  | let₁ ha _ ih => exact .let₁ (ha.subst (valuesTyped hθ)) (ih (liftValues hθ _))
  | let₂ ha _ ih => exact .let₂ (ha.subst (valuesTyped hθ)) (ih (liftValues (liftValues hθ _) _))
  | case ha _ _ ihl ihr =>
    exact .case (ha.subst (valuesTyped hθ)) (ihl (liftValues hθ _)) (ihr (liftValues hθ _))
  | cfg R _ _ ihe ihb => exact .cfg R (ihe hθ) (fun i => ihb i (liftValues hθ _))

private theorem mapReentry (θ : Nat → Tm Φ) (block : Region Φ) :
    mapLSubstVars θ (reentry block) = reentry (block.substVars (Tm.liftSubst θ)) := by
  funext i
  simp only [mapLSubstVars, reentry, cfgEntryContinuations, substVars, Tm.subst, Tm.liftSubst,
    substVars_renameVars, renameVars_substVars, Tm.liftSubst_comp_lift_succ]

theorem eqv_substVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {θ : Nat → Tm Φ}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    Eqv Δ (r.substVars θ) (s.substVars θ) L := by
  induction h generalizing Δ θ with
  | native h => exact .native (h.substVars hθ)
  | symm _ ih => exact .symm (ih hθ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hθ) (ih₂ hθ)
  | let₁ ha _ ih => exact .let₁ (ha.subst (valuesTyped hθ)) (ih (liftValues hθ _))
  | let₂ ha _ ih => exact .let₂ (ha.subst (valuesTyped hθ)) (ih (liftValues (liftValues hθ _) _))
  | case ha _ _ ihl ihr =>
    exact .case (ha.subst (valuesTyped hθ)) (ihl (liftValues hθ _)) (ihr (liftValues hθ _))
  | cfg R _ _ ihe ihb => exact .cfg R (ihe hθ) (fun i => ihb i (liftValues hθ _))
  | etaPost he hb hσ =>
    simpa only [substVars_lsubst, singleCfg, Region.substVars, mapReentry] using
      Eqv.etaPost (valueSubst he hθ) (valueSubst hb (liftValues hθ _)) (hσ.mapVars (valuesTyped hθ))

theorem eqv_renameVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) :
    Eqv Δ (r.renameVars ρ) (s.renameVars ρ) L := by
  rw [renameVars_eq_substVars, renameVars_eq_substVars]
  exact eqv_substVars h (fun _ _ hi => .var (hρ hi))

theorem equivalent_liftVars {Γ : VCtx τ} {L K : LCtx τ} {σ υ : Nat → Region Φ}
    (h : Equivalent Γ L K σ υ) (B : τ) :
    Equivalent (B :: Γ) L K (liftLSubstVars σ) (liftLSubstVars υ) :=
  fun _ A hi => eqv_renameVars (h hi) ((Ren.wk Γ B).lift A)

theorem equivalent_liftLabels {Γ : VCtx τ} {L K : LCtx τ} {σ υ : Nat → Region Φ}
    (h : Equivalent Γ L K σ υ) (B : τ) :
    Equivalent Γ (B :: L) (B :: K) (liftLSubst σ) (liftLSubst υ) := by
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .native (.base (.refl (.br rfl (.var rfl))))
  | succ i => exact eqv_renameLabels (h hi) (Ren.wk K B)

theorem equivalent_prefix {Γ : VCtx τ} {L K : LCtx τ} {σ υ : Nat → Region Φ}
    (h : Equivalent Γ L K σ υ) (Ξ : LCtx τ) :
    Equivalent Γ (Ξ ++ L) (Ξ ++ K) (liftLSubstN Ξ.length σ) (liftLSubstN Ξ.length υ) := by
  induction Ξ with
  | nil => exact h
  | cons B Ξ ih => exact equivalent_liftLabels ih B

theorem lsubst_congr {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {σ υ : Nat → Region Φ} (h : Equivalent Γ L K σ υ) :
    Eqv Γ (r.lsubst σ) (r.lsubst υ) K := by
  induction hr generalizing K σ υ with
  | br hi ha =>
    apply eqv_substVars (h hi)
    intro i A hvi
    cases i with
    | zero =>
      cases Option.some.inj hvi
      exact ha
    | succ i => exact .var hvi
  | let₁ ha _ ih => exact .let₁ ha (ih (equivalent_liftVars h _))
  | let₂ ha _ ih => exact .let₂ ha (ih (equivalent_liftVars (equivalent_liftVars h _) _))
  | case ha _ _ ihl ihr => exact .case ha (ihl (equivalent_liftVars h _)) (ihr (equivalent_liftVars h _))
  | cfg R _ _ ihe ihb =>
    have h' := equivalent_prefix h (List.ofFn R)
    simp only [List.length_ofFn] at h'
    exact .cfg R (ihe h') (fun i => ihb i (equivalent_liftVars h' _))

theorem eqv_typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L) :
    HasType Γ r L ∧ HasType Γ s L := by
  induction h with
  | native h => exact h.typed
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ia ib => exact ⟨ia.1, ib.2⟩
  | let₁ ha _ ih => exact ⟨.let₁ ha ih.1, .let₁ ha ih.2⟩
  | let₂ ha _ ih => exact ⟨.let₂ ha ih.1, .let₂ ha ih.2⟩
  | case ha _ _ ia ib => exact ⟨.case ha ia.1 ib.1, .case ha ia.2 ib.2⟩
  | cfg R _ _ ie ib => exact ⟨.cfg R ie.1 (fun i => (ib i).1), .cfg R ie.2 (fun i => (ib i).2)⟩
  | @etaPost Γ entry A L block K σ he hb hσ =>
    let R : Fin 1 → τ := fun _ => A
    have hbs (i : Fin 1) : HasType (R i :: Γ) block (List.ofFn R ++ L) := hb.hasType
    exact ⟨(HasType.cfg R he.hasType hbs).lsubst hσ,
      (he.hasType.lsubst (cfgEntryContinuations_hasType R hbs)).lsubst hσ⟩

private theorem singleFamily {Γ : VCtx τ} {A : τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches (A :: Γ) r L) : LSubst.ValueFamily Γ [A] L (fun _ => r) := by
  intro i D hi
  have eq : D = A := List.mem_singleton.mp (List.mem_of_getElem? hi)
  cases eq
  exact hr

private theorem weaken {Γ : VCtx τ} {A : τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches (A :: Γ) r L) (B : τ) :
    ValueBranches (A :: B :: Γ) (r.renameVars (lift Nat.succ)) L :=
  valueFamily_liftVars (singleFamily hr) B (ℓ := 0) (A := A) rfl

private theorem cfg_values {Γ : VCtx τ} {A : τ} {L : LCtx τ} {entry b : Region Φ}
    (he : ValueBranches Γ entry (A :: L)) (hb : ValueBranches (A :: Γ) b (A :: L)) :
    ValueBranches Γ (singleCfg entry b) L :=
  .cfg (fun _ : Fin 1 => A) he (fun _ => hb)

theorem reentry_values {Γ : VCtx τ} {A : τ} {L : LCtx τ} {b : Region Φ}
    (hb : ValueBranches (A :: Γ) b (A :: L)) :
    LSubst.ValueFamily Γ (A :: L) L (reentry b) := by
  intro i T hi
  exact .cfg (fun _ : Fin 1 => A) (.br hi (.var (i := 0) rfl)) (fun _ => weaken hb T)

theorem eqv_bindBranchArguments {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) : Eqv Γ r.bindBranchArguments s.bindBranchArguments L := by
  induction h with
  | native h => exact .native h.bindBranchArguments
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | @etaPost Γ entry A L block K σ he hb hσ =>
    have hnormalized : LSubst.HasType Γ L K (fun i => (σ i).bindBranchArguments) :=
      fun _ _ hi => (hσ hi).bindBranchArguments.hasType
    exact (Eqv.native ((cfg_values he hb).normalize_lsubst hσ)).trans
      ((Eqv.etaPost he hb hnormalized).trans
       (.native ((valueBranches_lsubst he (reentry_values hb)).normalize_lsubst hσ).symm))

private theorem weakenTwice (r : Region Φ) :
    (r.renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ)) =
      (r.renameVars (lift Nat.succ)).renameVars (lift Nat.succ) := by
  rw [renameVars_comp, renameVars_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

private theorem shiftReentry (b : Region Φ) :
    liftLSubstVars (reentry b) = reentry (b.renameVars (lift Nat.succ)) := by
  funext i
  simp only [liftLSubstVars, reentry, cfgEntryContinuations, renameVars, Tm.rename, weakenTwice]
  rfl

/-- The one-local-label specialization of companion Eqv.seq_cont.
The producer can contain arbitrary typed computations and nested CFGs. -/
theorem seqCont {Γ : VCtx τ} {A S : τ} {L : LCtx τ} {p d b : Region Φ}
    (hp : ValueBranches Γ p [S]) (hd : ValueBranches (S :: Γ) d (A :: L))
    (hb : ValueBranches (A :: Γ) b (A :: L)) :
    Eqv Γ (singleCfg (p.lsubst (fun _ => d)) b)
      (p.lsubst (fun _ => singleCfg d (b.renameVars (lift Nat.succ)))) L := by
  have hη := eta (valueBranches_lsubst hp (singleFamily hd)) hb
  rw [lsubst_comp] at hη
  apply hη.trans
  apply lsubst_congr hp
  intro i D hi
  have eq : D = S := List.mem_singleton.mp (List.mem_of_getElem? hi)
  cases eq
  have step := (eta hd (weaken hb S)).symm
  simpa only [compLSubst, shiftReentry] using step

open SyntacticCategory (iterateRegion iterationBody iterationDispatch iterationDispatch_valueBranches)

private theorem weakenArms (r : Region Φ) :
    (r.renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ)) =
      r.renameVars (lift (Nat.succ ∘ Nat.succ)) := by
  rw [weakenTwice, renameVars_comp]
  congr 1
  funext i
  cases i <;> rfl

private theorem body_values {Γ : VCtx τ} {A B : τ} {p : Region Φ}
    (hp : ValueBranches (A :: Γ) p [Silmaril.coprod B A]) :
    ValueBranches (A :: Γ) (iterationBody p) [A, B] :=
  valueBranches_lsubst hp (singleFamily (iterationDispatch_valueBranches A B))

/-- The full one-input arrow law in the extended native relation, including
producers with effects and nested, recursive CFGs. -/
theorem fixpoint {Γ : VCtx τ} {A B : τ} {p : Region Φ}
    (hp : ValueBranches (A :: Γ) p [Silmaril.coprod B A]) :
    Eqv (A :: Γ) (iterateRegion A p) (p.lsubst (fun _ => returnOrRepeat A p)) [B] := by
  let S := Silmaril.coprod B A
  have hu := Eqv.native (SyntacticCategory.iterateRegion_unfold hp)
  have hd := iterationDispatch_valueBranches (Φ := Φ) (Γ := A :: Γ) A B
  have hs := seqCont hp hd (weaken (body_values hp) A)
  refine hu.trans (hs.trans (lsubst_congr hp ?_))
  intro i D hi
  have eq : D = S := List.mem_singleton.mp (List.mem_of_getElem? hi)
  cases eq
  have hcase := eqv_renameVars (Eqv.native (SyntacticCategory.iterationDispatch_cfg hp))
    ((Ren.wk Γ A).lift S)
  change Eqv (S :: A :: Γ)
    (singleCfg iterationDispatch (((iterationBody p).renameVars (lift Nat.succ)).renameVars
      (lift (lift Nat.succ))))
    (.case (.var 0) (.br 0 (.var 0))
      (((iterateRegion A p).renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ)))) [B] at hcase
  rw [weakenTwice (iterationBody p), weakenArms] at hcase
  exact hcase

/-- For arbitrary exact typing, bind branch arguments once before interpreting
the producer as a continuation-category arrow. -/
theorem fixpoint_afterBinding {Γ : VCtx τ} {A B : τ} {p : Region Φ}
    (hp : HasType (A :: Γ) p [Silmaril.coprod B A]) :
    Eqv (A :: Γ) (iterateRegion A p.bindBranchArguments)
      (p.bindBranchArguments.lsubst (fun _ => returnOrRepeat A p.bindBranchArguments)) [B] :=
  fixpoint hp.bindBranchArguments

/-- Composition on typed value families respects the repaired pointwise
relation in both arguments. -/
theorem equivalent_comp {Γ : VCtx τ} {L K H : LCtx τ} {σ σ' υ υ' : Nat → Region Φ}
    (hσ : Equivalent Γ L K σ σ') (hυ : Equivalent Γ K H υ υ')
    (hvalues : LSubst.ValueFamily Γ L K σ) :
    Equivalent Γ L H (compLSubst σ υ) (compLSubst σ' υ') := by
  intro i A hi
  have h := equivalent_liftVars hυ A
  exact (lsubst_congr (hvalues hi) h).trans
    (eqv_lsubst (hσ hi) (fun _ _ hj => (eqv_typed (h hj)).2))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta
