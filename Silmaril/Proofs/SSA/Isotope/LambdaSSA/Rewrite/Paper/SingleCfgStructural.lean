module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Factor.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Thms

/-! # Exact comparison of structural carried-step factors -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgStructural

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open Paper.SingletonReification.SingleCfg
open Paper.PackedBody (applyPacked applyPacked_typed)
open CfgEta.TypeCategory (whiskerLeftRegion whiskerLeftBody whiskerLeftRegion_typed
  whiskerLeftBody_typed seqValueBranches productSndBranches singletonValueFamily)
open SyntacticCategory (iterateRegion_valueBranches)
open Paper.TypeCategory (ofType ofRegion sumIso whiskerLeft whiskerLeft_ofRegion ofRegion_comp
  ofRegion_eq_iff iterateSum iterateSum_ofRegion)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.SingletonReification (ModelComparisons)
open Paper.RetainedCase (reindexHom)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v u₁ v₁ w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X S D : τ}

theorem duplicateCapture_typed (X S : τ) :
    ValueBranches [product X S] (duplicateCapture : Region Φ) [product X (product X S)] :=
  .let₂ (.var (i := 0) rfl) (.br rfl (.pair (.var (i := 1) rfl)
    (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))

set_option backward.isDefEq.respectTransparency false in
theorem retagPacked_typed (X S D : τ) :
    ValueBranches [product X (packedExitType [S, D])] (retagPacked (Φ := Φ) S D)
      [coprod (product X D) (product X S)] :=
  .let₂ (.var (i := 0) rfl)
    (((unpackExits_valueFamily [X, product X (packedExitType [S, D])] [S, D])
      (ℓ := 0) (A := packedExitType [S, D]) rfl).lsubst (tagCarriedExit_valueFamily _ _))

private def pairExit : Nat → Region Φ :=
  fun _ => .br 0 (.pair (.var 2) (.var 0))

private def afterWhisker (b : Region Φ) : Region Φ :=
  .let₂ (.var 0) (((applyPacked b).renameVars (lift (lift Nat.succ))).lsubst pairExit)

set_option backward.isDefEq.respectTransparency false in
private theorem duplicateCapture_whisker {B : τ} {b : Region Φ} (hb : ValueBranches [product X S] b [B]) :
    Paper.Eqv [product X S]
      (compLSubst (fun _ => duplicateCapture) (fun _ => whiskerLeftRegion b) 0)
      (afterWhisker b) [product X B] := by
  let P := product X S
  let Q := product X P
  let t : Tm Φ := .pair (.var 1) (.pair (.var 1) (.var 0))
  have hX : Tm.BranchValue [S, X, P] (.var 1 : Tm Φ) X := .var (i := 1) rfl
  have hS : Tm.BranchValue [S, X, P] (.var 0 : Tm Φ) S := .var (i := 0) rfl
  have ht : Tm.HasType [S, X, P] t Q := (hX.pair (hX.pair hS)).hasType
  let ρ := Nat.succ ∘ Nat.succ ∘ Nat.succ
  have w : Ren ([] : VCtx τ) [S, X, P] ρ :=
    ((Ren.wk [] P).comp (Ren.wk [P] X)).comp (Ren.wk [X, P] S)
  let h := (whiskerLeftBody_typed X hb).hasType.renameVars (((w.lift Q).lift X).lift P)
  have hb' := h.substVars (((Tm.Subst.HasType.single ht).lift X).lift P)
  have eq := Paper.Eqv.productBeta (.let₂Beta hX (hX.pair hS) hb')
  simp only [compLSubst, duplicateCapture, lsubst, afterWhisker, liftLSubstVars,
    renameVars_comp, ← Silmaril.DeBruijn.lift_comp]
  apply Paper.Eqv.let₂ (.var (i := 0) rfl)
  -- The inner product beta exposes the original pair at the guarded body's input.
  refine eq.trans ?_
  have same : ((((whiskerLeftBody b).renameVars (lift (lift (lift ρ)))).substVars
      (Tm.liftSubstN 2 (Tm.singleSubst t))).substVars
      (Tm.consSubst (.pair (.var 1) (.var 0)) (Tm.singleSubst (.var 1)))) =
      (((applyPacked b).renameVars (lift (lift Nat.succ))).lsubst pairExit) := by
    simp only [whiskerLeftBody, substVars_comp, renameVars_lsubst, renameVars_comp,
      substVars_lsubst, substVars_renameVars, applyPacked, renameVars_substVars]
    congr 1
    apply singleton_subst hb.hasType
    rfl
  rw [← same]
  exact .refl eq.typed.2


set_option backward.isDefEq.respectTransparency false in
private theorem retag_pair (X S D : τ) :
    let P := product X S
    let K := packedExitType [S, D]
    Paper.Eqv [K, S, X, P]
      (compLSubst pairExit (liftLSubstVars (liftLSubstVars (liftLSubstVars
        (fun _ => retagPacked (Φ := Φ) S D)))) 0)
      (((unpackExits [S, D]).renameVars (lift (lift (lift Nat.succ)))).lsubst
        (liftLSubstVars tagCarriedExit)) [coprod (product X D) (product X S)] := by
  dsimp only
  let P := product X S
  let K := packedExitType [S, D]
  let Q := product X K
  let R := coprod (product X D) (product X S)
  let Γ := [K, S, X, P]
  let t : Tm Φ := .pair (.var 2) (.var 0)
  let ρ := Nat.succ ∘ Nat.succ ∘ Nat.succ ∘ Nat.succ
  have w : Ren ([] : VCtx τ) Γ ρ :=
    (((Ren.wk [] P).comp (Ren.wk [P] X)).comp (Ren.wk [X, P] S)).comp (Ren.wk [S, X, P] K)
  have hX : Tm.BranchValue Γ (.var 2 : Tm Φ) X := .var (i := 2) rfl
  have hK : Tm.BranchValue Γ (.var 0 : Tm Φ) K := .var (i := 0) rfl
  have ht : Tm.HasType Γ t Q := (hX.pair hK).hasType
  have hd : ValueBranches [K, X, Q] ((unpackExits [S, D]).lsubst (tagCarriedExit (Φ := Φ))) [R] :=
    (((unpackExits_valueFamily [X, Q] [S, D]) (ℓ := 0) (A := K) rfl).lsubst (tagCarriedExit_valueFamily _ _))
  have hb := (hd.hasType.renameVars (((w.lift Q).lift X).lift K)).substVars
    (((Tm.Subst.HasType.single ht).lift X).lift K)
  have eq := Paper.Eqv.productBeta (.let₂Beta hX hK hb)
  simp only [compLSubst, pairExit, lsubst, liftLSubstVars, retagPacked, renameVars_comp,
    ← Silmaril.DeBruijn.lift_comp]
  refine eq.trans ?_
  have same : ((((unpackExits [S, D]).lsubst (tagCarriedExit (Φ := Φ))).renameVars
        (lift (lift (lift ρ)))).substVars (Tm.liftSubst (Tm.liftSubst (Tm.singleSubst t)))).substVars
        (Tm.consSubst (.var 0) (Tm.singleSubst (.var 2))) =
      (((unpackExits [S, D]).renameVars (lift (lift (lift Nat.succ)))).lsubst
        (liftLSubstVars tagCarriedExit)) := by
    simp only [substVars_comp, renameVars_lsubst, substVars_lsubst,
      renameVars_eq_substVars (unpackExits [S, D])]
    congr 1
    · funext i
      cases i <;> rfl
  rw [← same]
  exact .refl eq.typed.2


set_option backward.isDefEq.respectTransparency false in
theorem realizePackedStep_factor {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) :
    Paper.Eqv [product X S]
      (compLSubst (compLSubst (fun _ => duplicateCapture) (fun _ => whiskerLeftRegion b))
        (fun _ => retagPacked S D) 0)
      (realizePackedStep S D b) [coprod (product X D) (product X S)] := by
  let P := product X S
  let K := packedExitType [S, D]
  let Q := product X K
  let R := coprod (product X D) (product X S)
  have hp := (applyPacked_typed hb).renameVars (((Ren.wk [] P).lift X).lift S)
  have hPair : LSubst.ValueFamily (Φ := Φ) [S, X, P] [K] [Q] pairExit := by
    intro i A hi
    cases List.mem_singleton.mp (List.mem_of_getElem? hi)
    exact .br rfl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))
  have hAfter : ValueBranches [P] (afterWhisker b) [Q] :=
    .let₂ (.var (i := 0) rfl) (hp.lsubst hPair)
  have hpost := (duplicateCapture_whisker hb).lsubstPost
    (seqValueBranches (duplicateCapture_typed X S) (whiskerLeftRegion_typed X hb)) hAfter
    (K := [R]) (σ := liftLSubstVars (fun _ => retagPacked (Φ := Φ) S D))
    (fun _ _ hi => ((CfgEta.TypeCategory.singletonValueFamily
      (retagPacked_typed (Φ := Φ) X S D)).liftVars P hi).hasType)
  change Paper.Eqv [P] _ _ [R] at hpost
  refine hpost.trans ?_
  unfold realizePackedStep realizeStep
  apply Paper.Eqv.let₂ (.var (i := 0) rfl)
  let w := ((Ren.wk [] P).lift X).lift S
  have hb0 := applyPacked_typed hb
  have hLinked := (decodeExits_eq_lsubst hb0).renameVars w
  have hTag := tagCarriedExit_valueFamily (Φ := Φ) (X := X) (S := S) (D := D) S P
  have hpost' := hLinked.lsubstPost ((decodeExits_typed hb0).renameVars w)
    ((hb0.lsubst (fun _ _ hi => (unpackExits_valueFamily [S, X] [S, D]) hi)).renameVars w)
    (fun _ _ hi => (hTag hi).hasType)
  refine Paper.Eqv.trans ?_ hpost'.symm
  simp only [renameVars_lsubst, lsubst_comp]
  apply Paper.Eqv.lsubstCongr hp
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact retag_pair X S D
  | succ i => simp [At] at hi


set_option backward.isDefEq.respectTransparency false in
theorem realizePackedStep_arrow {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) :
    (ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S) ≫ whiskerLeft (ofType X) (ofRegion (τ := τ) hb)) ≫
      ofRegion (τ := τ) (retagPacked_typed (Φ := Φ) X S D) = ofRegion (τ := τ) (realizePackedStep_typed hb) := by
  rw [whiskerLeft_ofRegion, ofRegion_comp _ _ (seqValueBranches (duplicateCapture_typed X S) (whiskerLeftRegion_typed X hb)),
    ofRegion_comp _ _ (seqValueBranches (seqValueBranches (duplicateCapture_typed X S)
      (whiskerLeftRegion_typed X hb)) (retagPacked_typed X S D))]
  exact (ofRegion_eq_iff _ _).2 (realizePackedStep_factor hb)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalExitContinuation_congr {s t : Region Φ}
    (hs : ValueBranches [product X S] s [coprod (product X D) (product X S)])
    (ht : ValueBranches [product X S] t [coprod (product X D) (product X S)])
    (h : ofRegion (τ := τ) hs = ofRegion (τ := τ) ht) :
    Paper.Eqv [packedExitType [S, D], X] (canonicalExitContinuation X S s)
      (canonicalExitContinuation X S t) [D] := by
  let P := product X S
  let K := packedExitType [S, D]
  let U := coprod D S
  have hloop := congrArg iterateSum h
  rw [iterateSum_ofRegion (τ := τ) hs, iterateSum_ofRegion (τ := τ) ht] at hloop
  have hloops := (ofRegion_eq_iff _ _).1 hloop
  have hproject := hloops.lsubstPost (iterateRegion_valueBranches hs) (iterateRegion_valueBranches ht)
    (K := [D]) (fun _ _ hi => ((singletonValueFamily (productSndBranches (Φ := Φ) X D)).liftVars P hi).hasType)
  have hpacked : Paper.Eqv [S, X] (applyPacked _) (applyPacked _) [D] :=
    hproject.substVars (by
      intro i A hi
      cases i with
      | zero =>
        cases Option.some.inj hi
        exact .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
      | succ i => simp [At] at hi)
  have hcase := Paper.Eqv.case (.var (i := 0) (show At [U, X] 0 U from rfl))
    (.refl ((applyPacked_typed (productSndBranches (Φ := Φ) X D)).hasType.renameVars ((Ren.wk [X] U).lift D)))
    (hpacked.renameVars ((Ren.wk [X] U).lift S))
  exact Paper.lsubst_singleton_congr ((exitDecoder_typed (Φ := Φ) S D).renameVars ((Ren.wk [] X).lift K))
    (hcase.renameVars ((Ren.wk [X] K).lift U))

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {ε : Type w} [HasEff Φ ε] {pe : ε}

set_option backward.isDefEq.respectTransparency false in
theorem carriedStep_eq_realizePackedStep {b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (prefixEq : capturePrefix J M objIso X S = ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S))
    (routeEq : carriedRoute J M objIso X S D =
      ofRegion (τ := τ) (retagPacked_typed (Φ := Φ) X S D) ≫ (sumIso (product X D) (product X S)).hom) :
    carriedStep J M objIso X S D ((objIso (product X S)).hom ≫
      ofRegion (τ := τ) hb ≫ (objIso (packedExitType [S, D])).inv) =
      ofRegion (τ := τ) (realizePackedStep_typed hb) ≫ (sumIso (product X D) (product X S)).hom := by
  have blockEq : reindexHom J M objIso ((objIso (product X S)).hom ≫
      ofRegion (τ := τ) hb ≫ (objIso (packedExitType [S, D])).inv) = ofRegion (τ := τ) hb := by simp [reindexHom]
  rw [carriedStep_factor _ _ _ (fun f => cmp.whisker f), blockEq, prefixEq, routeEq]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ (sumIso (Φ := Φ) (product X D) (product X S)).hom) (realizePackedStep_arrow hb)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalExitContinuation_eq_of_carriedStep {b step : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (hs : ValueBranches [product X S] step [coprod (product X D) (product X S)])
    (prefixEq : capturePrefix J M objIso X S = ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S))
    (routeEq : carriedRoute J M objIso X S D =
      ofRegion (τ := τ) (retagPacked_typed (Φ := Φ) X S D) ≫ (sumIso (product X D) (product X S)).hom)
    (hStep : carriedStep J M objIso X S D ((objIso (product X S)).hom ≫
      ofRegion (τ := τ) hb ≫ (objIso (packedExitType [S, D])).inv) =
        ofRegion (τ := τ) hs ≫ (sumIso (product X D) (product X S)).hom) :
    Paper.Eqv [packedExitType [S, D], X] (canonicalExitContinuation X S step)
      (carriedExitContinuation X S D b) [D] := by
  have h := hStep.symm.trans (carriedStep_eq_realizePackedStep J M objIso cmp hb prefixEq routeEq)
  apply (canonicalExitContinuation_congr hs (realizePackedStep_typed hb) ?_).trans (realize_exitContinuation hb)
  apply (cancel_mono (sumIso (Φ := Φ) (product X D) (product X S)).hom).1
  exact h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgStructural
