module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Outward.Thms

/-! # Proofs of literal retained unary let -/

public section

open Silmaril
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open CfgEta.TypeCategory
open Silmaril.DeBruijn (lift)

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLet

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B : τ} {a : Tm Φ} {r : Region Φ}

open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem agree_lift {Γ : VCtx τ} {σ η : Nat → Tm Φ}
    (h : ∀ i C, At Γ i C → σ i = η i) (D : τ) :
    ∀ i C, At (D :: Γ) i C → Tm.liftSubst σ i = Tm.liftSubst η i := by
  intro i C hi
  cases i with
  | zero => rfl
  | succ i => exact congrArg (Tm.rename Nat.succ) (h i C hi)

theorem term_subst_eq {Γ : VCtx τ} (ha : Tm.HasType Γ a A)
    {σ η : Nat → Tm Φ} (h : ∀ i C, At Γ i C → σ i = η i) :
    a.subst σ = a.subst η := by
  induction ha generalizing σ η with
  | var hi => exact h _ _ hi
  | op _ ih => simp only [Tm.subst, ih h]
  | let₁ _ _ ih₁ ih₂ => simp only [Tm.subst, ih₁ h, ih₂ (agree_lift h _)]
  | pair _ _ ih₁ ih₂ => simp only [Tm.subst, ih₁ h, ih₂ h]
  | unit => rfl
  | let₂ _ _ ih₁ ih₂ =>
    simp only [Tm.subst, Tm.liftSubstN, ih₁ h, ih₂ (agree_lift (agree_lift h _) _)]
  | inl _ ih => simp only [Tm.subst, ih h]
  | inr _ ih => simp only [Tm.subst, ih h]
  | case _ _ _ ih₁ ih₂ ih₃ => simp only [Tm.subst, ih₁ h, ih₂ (agree_lift h _), ih₃ (agree_lift h _)]
  | abort _ ih => simp only [Tm.subst, ih h]

private def returnWithInput (a : Tm Φ) : Region Φ :=
  .let₁ a (.br 0 (.pair (.var 1) (.var 0)))

private theorem returnWithInput_typed (ha : Tm.HasType [X] a A) :
    ValueBranches [X] (returnWithInput a) [Silmaril.product X A] :=
  .let₁ ha (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))

/-- Constructor β contracts the duplicated input, leaving the scrutinee
in its original context and retaining the input beside its value. -/
private theorem duplicate_whisker_returnOnce (ha : Tm.HasType [X] a A) :
    Paper.Eqv [X]
      (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion (returnOnce a)) 0)
      (returnWithInput a) [Silmaril.product X A] := by
  let P := Silmaril.product X X
  let pairTerm := Tm.pair (.var 0) (.var 0) (Φ := Φ)
  let σ := Tm.liftSubstN 2 (Tm.singleSubst pairTerm)
  let κ := Tm.consSubst (.var 0) (Tm.singleSubst (.var 0 : Tm Φ))
  let b := whiskerLeftBody (returnOnce a)
  let υ := lift (lift (lift Nat.succ))
  have hp : Tm.BranchValue [X] pairTerm P := .pair (.var (i := 0) rfl) (.var (i := 0) rfl)
  have hb : Region.HasType [X, X, X] ((b.renameVars υ).substVars σ) [Silmaril.product X A] :=
    ((whiskerLeftBody_typed X (returnOnce_typed ha)).hasType.renameVars
      ((((Ren.wk ([] : VCtx τ) X).lift P).lift X).lift X)).substVars
      (((Tm.Subst.HasType.single hp.hasType).lift X).lift X)
  have hβ := Paper.Eqv.productBeta (.let₂Beta (.var (i := 0) (rfl : At [X] 0 X))
    (.var (i := 0) (rfl : At [X] 0 X)) hb)
  change Paper.Eqv [X] (.let₂ pairTerm ((b.renameVars υ).substVars σ))
    (((b.renameVars υ).substVars σ).substVars κ) [Silmaril.product X A] at hβ
  have ha' : ((((a.rename (lift (Nat.succ ∘ Nat.succ))).rename υ).subst σ).subst κ) = a := by
    rw [Tm.rename_comp, Tm.subst_comp, Tm.subst_rename]
    refine (term_subst_eq ha (η := Tm.var) ?_).trans (Tm.subst_var a)
    intro i C hi
    cases i with
    | zero => rfl
    | succ i => simp [At] at hi
  have eq : ((b.renameVars υ).substVars σ).substVars κ = returnWithInput a := by
    change Region.let₁ ((((a.rename (lift (Nat.succ ∘ Nat.succ))).rename υ).subst σ).subst κ)
      (.br 0 (.pair (.var 1) (.var 0))) = _
    rw [ha']
    rfl
  rw [eq] at hβ
  exact hβ

/-- A retained arbitrary scrutinee followed by unpacking computes literal
unary let at exactly the context of its body. -/
private theorem returnWithInput_unpack (ha : Tm.HasType [X] a A) (hr : Region.HasType [A, X] r [B]) :
    Paper.Eqv [X] (compLSubst (fun _ => returnWithInput a) (fun _ => unpackBody r) 0)
      (.let₁ a r) [B] := by
  let P := Silmaril.product X A
  let pairTerm := Tm.pair (.var 1) (.var 0) (Φ := Φ)
  let ρ := lift (lift Nat.succ)
  let υ := lift (lift (lift (Nat.succ ∘ Nat.succ)))
  let σ := Tm.liftSubstN 2 (Tm.singleSubst pairTerm)
  let κ := Tm.consSubst (.var 0) (Tm.singleSubst (.var 1 : Tm Φ))
  have hp : Tm.BranchValue [A, X] pairTerm P := .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  have hCapture : Ren ([] : VCtx τ) [A, X] (Nat.succ ∘ Nat.succ) := by
    intro i C hi
    simp [At] at hi
  have hb : Region.HasType [A, X, A, X] (((r.renameVars ρ).renameVars υ).substVars σ) [B] :=
    ((hr.renameVars (((Ren.wk ([] : VCtx τ) P).lift X).lift A)).renameVars
      (((hCapture.lift P).lift X).lift A)).substVars (((Tm.Subst.HasType.single hp.hasType).lift X).lift A)
  have step := Paper.Eqv.productBeta (.let₂Beta (.var (i := 1) (rfl : At [A, X] 1 X))
    (.var (i := 0) (rfl : At [A, X] 0 A)) hb)
  change Paper.Eqv [A, X] (.let₂ pairTerm (((r.renameVars ρ).renameVars υ).substVars σ))
    ((((r.renameVars ρ).renameVars υ).substVars σ).substVars κ) [B] at step
  have sameSubst : (((r.renameVars ρ).renameVars υ).substVars σ).substVars κ = r.substVars Tm.var := by
    rw [Region.substVars_comp, Region.renameVars_comp, Region.substVars_renameVars]
    congr 1
    funext i
    cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  rw [sameSubst, substVars_var] at step
  have eqL : compLSubst (fun _ => returnWithInput a) (fun _ => unpackBody r) 0 =
      .let₁ a (.let₂ pairTerm (((r.renameVars ρ).renameVars υ).substVars σ)) := by
    simp only [compLSubst, returnWithInput, lsubst, liftLSubstVars, unpackBody, Region.renameVars,
      Region.substVars, Tm.rename, Tm.subst, Region.renameVars_comp]
    congr 3
    congr 1
    funext i
    cases i with
    | zero => rfl
    | succ i => cases i with
      | zero => rfl
      | succ i => cases i <;> rfl
  rw [eqL]
  exact .let₁ ha step

/-- The retained composition for unary let is equivalent to literal let
for arbitrary typed scrutinees and arbitrary exactly typed bodies. -/
theorem literal_let (ha : Tm.HasType [X] a A) (hr : Region.HasType [A, X] r [B]) :
    Paper.Eqv [X]
      (compLSubst
        (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion (returnOnce a)))
        (fun _ => unpackBody r) 0)
      (.let₁ a r) [B] := by
  have h := duplicate_whisker_returnOnce ha
  have hp := seqValueBranches (diagonal_typed (Φ := Φ) X)
    (whiskerLeftRegion_typed X (returnOnce_typed ha))
  have hq := returnWithInput_typed ha
  have hk : LSubst.HasType [] [Silmaril.product X A] [B] (fun _ => unpackBody r) := by
    intro i D hi
    have eq : D = Silmaril.product X A := List.mem_singleton.mp (List.mem_of_getElem? hi)
    subst D
    exact .let₂ (.var (i := 0) rfl)
      (hr.renameVars (((Ren.wk ([] : VCtx τ) (Silmaril.product X A)).lift X).lift A))
  exact (h.lsubstPost hp hq (hk.liftVars X)).trans (returnWithInput_unpack ha hr)

section Denotation

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The explicit single-bind return evaluates the actual arbitrary term,
using the existing effect-preserving branch-bind equation. -/
theorem returnOnce_denotation (ha : Tm.HasType [X] a A)
    {f : J.obj (ctxObj M [X]) ⟶ J.obj (M.obj A)} (d : Denotes J M ha f) :
    denoteSingletonRegion J M (returnOnce_typed ha).hasType =
      J.map ((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ f := by
  unfold denoteSingletonRegion
  have hb := denoteRegion_branchBind J M (FreydCategory.CentralUnit.unit_central (J := J))
    (rfl : At [A] 0 A) ha
  change denoteRegion J M (.br (rfl : At [A] 0 A) ha) =
    denoteRegion J M (returnOnce_typed ha).hasType at hb
  rw [← hb]
  exact denoteSingletonRegion_br J M d

end Denotation

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLet
