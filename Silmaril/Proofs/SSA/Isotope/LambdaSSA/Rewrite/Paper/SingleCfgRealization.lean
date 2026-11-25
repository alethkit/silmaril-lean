module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Thms

/-! # Product and decoder reduction for the syntactic carried step -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgRealization

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.SingletonReification.SingleCfg
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory (productSndBranches seqValueBranches)
open SyntacticCategory (iterateRegion iterationDispatch iterationBody iterateRegion_valueBranches)
open Paper.PackedBody (applyPacked applyPacked_typed)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X S D : τ}

set_option backward.isDefEq.respectTransparency false in
theorem tagCarriedExit_valueFamily (K Z : τ) :
    LSubst.ValueFamily (Φ := Φ) [K, X, Z] [S, D]
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)] tagCarriedExit := by
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .br rfl (.inr (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))
  | succ i =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact .br rfl (.inl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))
    | succ i => simp [At] at hi

theorem realizeStep_typed {p : Region Φ} (hp : ValueBranches [S, X] p [S, D]) :
    ValueBranches [Silmaril.product X S] (realizeStep p)
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)] :=
  .let₂ (.var (i := 0) rfl)
    ((hp.renameVars (((Ren.wk [] (Silmaril.product X S)).lift X).lift S)).lsubst (tagCarriedExit_valueFamily _ _))

private theorem caseLeft {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
    (ha : Tm.BranchValue Γ a A) (hl : HasType (A :: Γ) l L) (hr : HasType (B :: Γ) r L) :
    Paper.Eqv Γ (.case (.inl a) l r) (l.substVars (Tm.singleSubst a)) L :=
  .cfgEta (.native ((SubstitutionEquiv.base (.caseInl ha.hasType hl hr)).trans (.letValue ha hl)))

private theorem caseRight {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
    (ha : Tm.BranchValue Γ a B) (hl : HasType (A :: Γ) l L) (hr : HasType (B :: Γ) r L) :
    Paper.Eqv Γ (.case (.inr a) l r) (r.substVars (Tm.singleSubst a)) L :=
  .cfgEta (.native ((SubstitutionEquiv.base (.caseInr ha.hasType hl hr)).trans (.letValue ha hr)))

private def blockTail (P : τ) : Nat → Region Φ :=
  liftLSubstN ([P] : LCtx τ).length (fun _ => dropCapture)

omit [TypeFormers τ] [HasTy Φ τ] in
/-- The outer feedback binder leaves label zero as a repeat and pushes the
result projection into the block's outward exits. -/
private theorem project_feedback (P : τ) (step : Region Φ) :
    ((iterateRegion P step).lsubst (liftLSubstVars (fun _ => dropCapture))) =
      feedbackRegion [P]
        (fun _ => (iterationBody step).lsubst (liftLSubstVars (blockTail P))) 0 := by
  simp only [iterateRegion, feedbackRegion, cfgEntryContinuations, lsubst, List.length_cons,
    List.length_nil, liftLSubstN, liftLSubst, labelId, blockTail]
  congr 1
  funext i
  rw [renameVars_lsubst]
  congr 1
  funext j
  cases j <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem carried_branch {Z : τ} {i : Nat} {A : τ} (hi : At [S, D] i A) :
    Paper.Eqv [A, S, X, Z]
      (compLSubst (compLSubst tagCarriedExit
        (liftLSubstVars (liftLSubstVars (fun _ => iterationDispatch))))
        (liftLSubstVars (liftLSubstVars (liftLSubstVars (blockTail (Silmaril.product X S))))) i)
      ((carryRepeat (Φ := Φ) i).renameVars (lift (lift (lift Nat.succ)))) [Silmaril.product X S, D] := by
  cases i with
  | zero =>
    cases Option.some.inj hi
    have h := caseRight (A := Silmaril.product X D)
      (Tm.BranchValue.pair (.var (i := 2) (show At [S, S, X, Z] 2 X from rfl))
        (.var (i := 0) (show At [S, S, X, Z] 0 S from rfl)))
      (.let₂ (.var (i := 0) rfl) (.br (ℓ := 1) rfl (.var (i := 0) rfl)) :
        HasType (Silmaril.product X D :: [S, S, X, Z])
          (.let₂ (.var 0) (.br 1 (.var 0)) : Region Φ) [Silmaril.product X S, D])
      (.br (ℓ := 0) rfl (.var (i := 0) rfl))
    exact h
  | succ i =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      have h := caseLeft (B := Silmaril.product X S)
        (Tm.BranchValue.pair (.var (i := 2) (show At [D, S, X, Z] 2 X from rfl))
          (.var (i := 0) (show At [D, S, X, Z] 0 D from rfl)))
        (.let₂ (.var (i := 0) rfl) (.br (ℓ := 1) rfl (.var (i := 0) rfl)) :
          HasType (Silmaril.product X D :: [D, S, X, Z])
            (.let₂ (.var 0) (.br 1 (.var 0)) : Region Φ) [Silmaril.product X S, D])
        (.br (ℓ := 0) rfl (.var (i := 0) rfl))
      have β := Paper.Eqv.productBeta (ProductBeta.Step.let₂Beta
        (.var (i := 2) (show At [D, S, X, Z] 2 X from rfl))
        (.var (i := 0) (show At [D, S, X, Z] 0 D from rfl))
        (.br (ℓ := 1) rfl (.var (i := 0) rfl) :
          HasType [D, X, D, S, X, Z] (.br 1 (.var 0) : Region Φ) [Silmaril.product X S, D]))
      exact h.trans β
    | succ i => simp [At] at hi

set_option backward.isDefEq.respectTransparency false in
private theorem realize_block {p : Region Φ} (hp : ValueBranches [S, X] p [S, D]) :
    Paper.Eqv [Silmaril.product X S]
      ((iterationBody (realizeStep p)).lsubst (liftLSubstVars (blockTail (Silmaril.product X S))))
      (carryBlock p) [Silmaril.product X S, D] := by
  unfold iterationBody realizeStep carryBlock Paper.BoundSimulation.CapturedSquare.packedStep
    Paper.RetainedLet.unpackBody
  simp only [lsubst, renameVars_lsubst]
  apply Paper.Eqv.let₂ (.var (i := 0) rfl)
  rw [lsubst_comp, lsubst_comp, ← compLSubst_assoc]
  apply Paper.Eqv.lsubstCongr
    (hp.renameVars (((Ren.wk [] (Silmaril.product X S)).lift X).lift S))
  intro i A hi
  exact carried_branch hi

set_option backward.isDefEq.respectTransparency false in
theorem realize_loop {p : Region Φ} (hp : ValueBranches [S, X] p [S, D]) :
    Paper.Eqv [Silmaril.product X S]
      ((iterateRegion (Silmaril.product X S) (realizeStep p)).lsubst (liftLSubstVars (fun _ => dropCapture)))
      (feedbackRegion [Silmaril.product X S] (fun _ => carryBlock p) 0) [D] := by
  rw [project_feedback]
  let P := Silmaril.product X S
  exact .cfg (fun _ : Fin 1 => P)
    (.refl (.br (ℓ := 0) rfl (.var (i := 0) rfl)))
    (fun _ => (realize_block hp).renameVars ((Ren.wk [] P).lift P))

private def packedDispatch (τ : Type u) (k : Region Φ) : Region Φ :=
  compLSubst (fun _ => (exitDecoder (τ := τ)).renameVars (lift Nat.succ))
    (fun _ => Paper.RetainedCase.boundCase (applyPacked dropCapture) (applyPacked k)) 0

private def repeatDispatch (k : Region Φ) : Nat → Region Φ
  | 0 => k.renameVars (lift Nat.succ)
  | i + 1 => .br i (.var 0)

private def unpackedDispatch (S D : τ) (k : Region Φ) : Region Φ :=
  compLSubst (fun _ => unpackExits [S, D])
    (compLSubst (CfgEta.Uniformity.localMap capturePair) (repeatDispatch k)) 0


omit [TypeFormers τ] [HasTy Φ τ] in
private theorem subst_case_arm (r : Region Φ) (ρ : Nat → Nat) (a : Tm Φ) :
    ((r.renameVars (lift Nat.succ)).renameVars (lift (lift ρ))).substVars
      (Tm.liftSubst (Tm.singleSubst a)) = r.renameVars (lift ρ) := by
  rw [Region.renameVars_comp, Region.substVars_renameVars, Region.renameVars_eq_substVars]
  congr 1
  funext i
  cases i <;> rfl

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem apply_case (l r : Region Φ) (ρ : Nat → Nat) (a : Tm Φ) :
    ((Paper.RetainedCase.boundCase l r).renameVars (lift ρ)).substVars (Tm.singleSubst a) =
      .case a (l.renameVars (lift ρ)) (r.renameVars (lift ρ)) := by
  simp only [Paper.RetainedCase.boundCase, Region.renameVars, Region.substVars, Tm.rename, Tm.subst,
    subst_case_arm]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem dispatch_compare {k : Region Φ} (hk : ValueBranches [Silmaril.product X S] k [D]) :
    Paper.Eqv [packedExitType [S, D], X] (packedDispatch τ k) (unpackedDispatch S D k) [D] := by
  let K := packedExitType [S, D]
  let T := Silmaril.coprod D (Silmaril.empty : τ)
  let ρ := Nat.succ ∘ Nat.succ
  let υ := Nat.succ ∘ ρ
  have hl := applyPacked_typed (productSndBranches (Φ := Φ) X D)
  have hr := applyPacked_typed hk
  have w : Ren [X] [S, K, X] ρ := (Ren.wk [X] K).comp (Ren.wk [K, X] S)
  have w' : Ren [X] [D, T, K, X] υ := ((Ren.wk [X] K).comp (Ren.wk [K, X] T)).comp (Ren.wk [T, K, X] D)
  simp only [packedDispatch, unpackedDispatch, exitDecoder, unpackExits, compLSubst,
    Region.renameVars, Region.renameLabels, lsubst, Tm.rename, liftLSubstVars, renameVars_comp,
    ← Silmaril.DeBruijn.lift_comp]
  apply Paper.Eqv.case (.var (i := 0) (show At [K, X] 0 (Silmaril.coprod S T) from rfl))
  · change Paper.Eqv [S, K, X]
      (((Paper.RetainedCase.boundCase (applyPacked dropCapture) (applyPacked k)).renameVars
        (lift ρ)).substVars (Tm.singleSubst (.inr (.var 0)))) _ [D]
    rw [apply_case]
    have h := caseRight (.var (i := 0) (show At [S, K, X] 0 S from rfl))
      (hl.renameVars (w.lift D)).hasType (hr.renameVars (w.lift S)).hasType
    refine h.trans ?_
    have same :
        ((applyPacked k).renameVars (lift ρ)).substVars (Tm.singleSubst (.var 0)) =
          (((CfgEta.Uniformity.localMap capturePair 0).lsubst (liftLSubstVars (repeatDispatch k))).renameVars
            (lift ρ)).substVars (Tm.singleSubst (.var 0)) := by
      simp only [applyPacked, CfgEta.Uniformity.localMap, capturePair, lsubst,
        liftLSubstVars, repeatDispatch, renameVars_comp, substVars_renameVars, renameVars_substVars,
        substVars_comp]
      apply singleton_subst hk.hasType
      rfl
    rw [← same]
    exact .refl ((hr.renameVars (w.lift S)).hasType.substVars
      (Tm.Subst.HasType.single (.var (i := 0) rfl)))
  · apply Paper.Eqv.case (.var (i := 0) (show At [T, K, X] 0 T from rfl))
    · change Paper.Eqv [D, T, K, X]
        (((Paper.RetainedCase.boundCase (applyPacked dropCapture) (applyPacked k)).renameVars
          (lift υ)).substVars (Tm.singleSubst (.inl (.var 0)))) (.br 0 (.var 0)) [D]
      rw [apply_case]
      have h := caseLeft (.var (i := 0) (show At [D, T, K, X] 0 D from rfl))
        (hl.renameVars (w'.lift D)).hasType (hr.renameVars (w'.lift S)).hasType
      refine h.trans ?_
      exact .productBeta (.let₂Beta
        (.var (i := 3) (show At [D, T, K, X] 3 X from rfl))
        (.var (i := 0) (show At [D, T, K, X] 0 D from rfl))
        (.br (ℓ := 0) rfl (.var (i := 0) rfl) : HasType [D, X, D, T, K, X] (.br 0 (.var 0)) [D]))
    · let Z : τ := Silmaril.empty
      have he : ValueBranches [Z, T, K, X] (unpackExits ([] : LCtx τ) : Region Φ) [D] :=
        (((emptyExit_typed (Φ := Φ) D).renameVars ((Ren.wk [] X).lift Z)).renameVars
          ((Ren.wk [X] K).lift Z)).renameVars ((Ren.wk [K, X] T).lift Z)
      exact .refl he.hasType

set_option backward.isDefEq.respectTransparency false in
private theorem unpackedDispatch_congr {k q : Region Φ}
    (h : Paper.Eqv [Silmaril.product X S] k q [D]) :
    Paper.Eqv [packedExitType [S, D], X] (unpackedDispatch S D k) (unpackedDispatch S D q) [D] := by
  let K := packedExitType [S, D]
  let P := Silmaril.product X S
  unfold unpackedDispatch
  rw [← compLSubst_assoc, ← compLSubst_assoc]
  apply Paper.Eqv.lsubstCongr
  · have embed : LSubst.ValueFamily (Φ := Φ) [X] [S, D] [P, D] (CfgEta.Uniformity.localMap capturePair) := by
      intro i A hi
      cases i with
      | zero => cases Option.some.inj hi; exact .br rfl capturePair_typed
      | succ i => exact .br hi (.var (i := 0) rfl)
    exact ((unpackExits_valueFamily [X] [S, D]) (ℓ := 0) (A := K) rfl).lsubst (embed.liftVars K)
  · intro i A hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact (h.renameVars ((Ren.wk [] X).lift P)).renameVars ((Ren.wk [X] K).lift P)
    | succ i => exact .refl (.br (show At [D] i A from hi) (.var (i := 0) rfl))

theorem realizePackedStep_typed {b : Region Φ}
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    ValueBranches [Silmaril.product X S] (realizePackedStep S D b)
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)] :=
  realizeStep_typed (decodeExits_typed (applyPacked_typed hb))

set_option backward.isDefEq.respectTransparency false in
theorem realize_exitContinuation {b : Region Φ}
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    Paper.Eqv [packedExitType [S, D], X]
      (canonicalExitContinuation X S (realizePackedStep S D b)) (carriedExitContinuation X S D b) [D] := by
  have hk := seqValueBranches (iterateRegion_valueBranches (realizePackedStep_typed hb))
    (productSndBranches (Φ := Φ) X D)
  exact (dispatch_compare hk).trans (unpackedDispatch_congr (realize_loop (decodeExits_typed (applyPacked_typed hb))))

theorem canonicalRegion_eq_guardedCfg_realize {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    Paper.Eqv [X] (canonicalRegion X S e (realizePackedStep S D b)) (guardedCfg S D e b) [D] :=
  canonicalRegion_eq_guardedCfg_of_exitContinuation he hb (realizePackedStep_typed hb)
    (realize_exitContinuation hb)

open CategoryTheory
open Paper.TypeCategory (ofRegion sumIso ofRegion_eq_iff)

theorem canonicalRegion_eq_guardedCfg_of_stepArrow {e b step : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]])
    (hs : ValueBranches [Silmaril.product X S] step
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)])
    (h : ofRegion (τ := τ) hs ≫ (sumIso (Silmaril.product X D) (Silmaril.product X S)).hom =
      ofRegion (τ := τ) (realizePackedStep_typed hb) ≫
        (sumIso (Silmaril.product X D) (Silmaril.product X S)).hom) :
    Paper.Eqv [X] (canonicalRegion X S e step) (guardedCfg S D e b) [D] := by
  apply (ofRegion_eq_iff (canonicalRegion_typed he hs) (guardedCfg_typed he hb)).1
  rw [← canonicalAssembly_ofRegion he hs, h, canonicalAssembly_ofRegion he (realizePackedStep_typed hb)]
  exact (ofRegion_eq_iff _ _).2 (canonicalRegion_eq_guardedCfg_realize he hb)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgRealization
