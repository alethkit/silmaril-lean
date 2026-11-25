module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgCase.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies
import Silmaril.Raw.SSA.Isotope.LambdaSSA.Substitution

/-! # Exact typing and one-step unfolding for syntactic type iteration -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.SSA (Ren)
open SyntacticCategory (iterate iterateRegion iterationBody iterationDispatch
  iterationDispatch_valueBranches ofRegion)
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {A B : τ} {r : Region Φ}

private theorem iterationBody_valueBranches (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    ValueBranches (A :: Γ) (iterationBody r) [A, B] := by
  refine valueBranches_lsubst hr ?_
  intro i D hi
  have eq : D = Silmaril.coprod B A := List.mem_singleton.mp (List.mem_of_getElem? hi)
  cases eq
  exact iterationDispatch_valueBranches A B

private theorem iterationBody_valueFamily (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    LSubst.ValueFamily Γ [A] ([A] ++ [B]) (fun _ => iterationBody r) := by
  intro i D hi
  have eq : D = A := List.mem_singleton.mp (List.mem_of_getElem? hi)
  cases eq
  exact iterationBody_valueBranches hr

theorem iterateRegion_valueBranches (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    ValueBranches (A :: Γ) (iterateRegion A r) [B] :=
  (iterationBody_valueFamily hr).feedbackRegion (show At [A] 0 A from rfl)

theorem iterate_ofRegion (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    iterate (ofRegion hr) = ofRegion (iterateRegion_valueBranches hr) := by
  apply InducedCategory.hom_ext
  apply ContinuationFamily.toHom_eq_iff.mpr
  intro i D hi
  cases i with
  | zero =>
      cases Option.some.inj hi
      exact .base (.refl (iterateRegion_valueBranches hr).hasType)
  | succ i => simp [At, SyntacticCategory.ofType, ContinuationContext.single] at hi

theorem iterateRegion_unfold (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    SubstitutionEquiv (A :: Γ) (iterateRegion A r)
      (.cfg (iterationBody r) 1 (fun _ => (iterationBody r).renameVars (lift Nat.succ))) [B] :=
  (iterationBody_valueFamily hr).feedbackRegion_unfold 0

theorem iterationDispatch_cfg (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    SubstitutionEquiv (Silmaril.coprod B A :: Γ)
      (.cfg iterationDispatch 1 (fun _ => (iterationBody r).renameVars (lift Nat.succ)))
      (.case (.var 0) (.br 0 (.var 0)) ((iterateRegion A r).renameVars (lift Nat.succ))) [B] := by
  let S := Silmaril.coprod B A
  let R : Fin 1 → τ := fun _ => A
  let blocks : Fin 1 → Region Φ := fun _ => (iterationBody r).renameVars (lift Nat.succ)
  have hb (i : Fin 1) : HasType (R i :: S :: Γ) (blocks i) (List.ofFn R ++ [B]) :=
    (iterationBody_valueBranches hr).hasType.renameVars ((Ren.wk Γ S).lift A)
  have hl : HasType (B :: S :: Γ) (.br 1 (.var 0) : Region Φ) (List.ofFn R ++ [B]) :=
    .br rfl (.var rfl)
  have hs : HasType (A :: S :: Γ) (.br 0 (.var 0) : Region Φ) (List.ofFn R ++ [B]) :=
    .br rfl (.var rfl)
  have push := SubstitutionEquiv.cfg_caseValue R
    (Tm.BranchValue.var (Φ := Φ) (Γ := S :: Γ) (i := 0) (A := S) rfl) hl hs hb
  have hx (i : Fin 1) : HasType (R i :: B :: S :: Γ)
      ((blocks i).renameVars (lift Nat.succ)) (List.ofFn R ++ [B]) :=
    (hb i).renameVars ((Ren.wk (S :: Γ) B).lift A)
  have hy (i : Fin 1) : HasType (R i :: A :: S :: Γ)
      ((blocks i).renameVars (lift Nat.succ)) (List.ofFn R ++ [B]) :=
    (hb i).renameVars ((Ren.wk (S :: Γ) A).lift A)
  refine push.trans (.case (.var rfl)
    (.base (.entry (.cfgBrExit R (ℓ := 0) rfl (.var rfl) hx))) ?_)
  have hrename : (iterateRegion A r).renameVars (lift Nat.succ) =
      .cfg (.br 0 (.var 0)) 1 (fun i => (blocks i).renameVars (lift Nat.succ)) := by
    simp only [iterateRegion, feedbackRegion, cfgEntryContinuations, renameVars, Tm.rename,
      renameVars_comp, blocks]
    congr 1
    funext i
    congr 1
    funext j
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  rw [hrename]
  exact .base (.refl (.cfg R hs hy))

theorem iterateRegion_return {b : Tm Φ} (hb : Tm.BranchValue (A :: Γ) b B) :
    SubstitutionEquiv (A :: Γ) (iterateRegion A (.br 0 (.inl b))) (.br 0 b) [B] := by
  let body := iterationBody (.br 0 (.inl b) : Region Φ)
  let R : Fin 1 → τ := fun _ => A
  let blocks : Fin 1 → Region Φ := fun _ => body.renameVars (lift Nat.succ)
  have hr : ValueBranches (A :: Γ) (.br 0 (.inl b)) [Silmaril.coprod B A] :=
    .br rfl (.inl hb)
  have hl : HasType (B :: A :: Γ) (.br 1 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
  have hs : HasType (A :: A :: Γ) (.br 0 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
  have step : SubstitutionEquiv (A :: Γ) body (.br 1 b) (List.ofFn R ++ [B]) :=
    (SubstitutionEquiv.base (.caseInl hb.hasType hl hs)).trans (.letValue hb hl)
  have hblocks (i : Fin 1) : HasType (R i :: A :: Γ) (blocks i) (List.ofFn R ++ [B]) :=
    (iterationBody_valueBranches hr).hasType.renameVars ((Ren.wk Γ A).lift A)
  exact (iterateRegion_unfold hr).trans
    ((SubstitutionEquiv.cfg R step (fun i => .base (.refl (hblocks i)))).trans
      (.base (.entry (.cfgBrExit R (ℓ := 0) rfl hb hblocks))))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
