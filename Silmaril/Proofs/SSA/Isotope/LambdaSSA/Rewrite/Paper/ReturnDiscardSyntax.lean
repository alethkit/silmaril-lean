module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Syntax.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # Syntactic discard and the singleton computation comparison -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDiscardSyntax

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.Extension
open CfgEta.TypeCategory (returnRegion returnRegion_typed returnRegion_branchValue seqValueBranches)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "U" => (Silmaril.unit : τ)

theorem returnDiscards_branchValue {Γ : VCtx τ} {A : τ} {a : Tm Φ}
    (ha : Tm.BranchValue Γ a A) : ReturnDiscards Seed Γ a := by
  have h : Eqv Seed Γ (returnRegion a) (.br 0 a) [A] :=
    .paper (.cfgEta (.native (.base (returnRegion_branchValue ha))))
  exact h.lsubstPost (returnRegion_typed ha.hasType) (.br rfl ha) (fun _ _ _ => .br (ℓ := 0) rfl .unit)

theorem returnDiscards_let₁ {Γ : VCtx τ} {A : τ} {a b : Tm Φ}
    (ha : Tm.HasType Γ a A) (da : ReturnDiscards Seed Γ a)
    (db : ReturnDiscards Seed (A :: Γ) b) : ReturnDiscards Seed Γ (.let₁ a b) := by
  unfold ReturnDiscards
  rw [returnRegion, lsubst_comp]
  have h : Eqv Seed Γ
      ((returnRegion a).lsubst (compLSubst (fun _ => returnRegion b) (fun _ => .br 0 .unit)))
      ((returnRegion a).lsubst (fun _ => .br 0 .unit)) [U] := by
    apply Eqv.lsubstCongr (returnRegion_typed ha)
    intro i D hi
    have e : D = A := List.mem_singleton.mp (List.mem_of_getElem? hi)
    subst D
    exact db
  exact h.trans da

theorem returnDiscards_op_branchValue {ε : Type w} [HasEff Φ ε] {pe : ε}
    (primitive : PrimitiveReturnsDiscard Seed pe) {Γ : VCtx τ} {f : Φ} {a : Tm Φ}
    (hf : IsPure pe f) (ha : Tm.BranchValue Γ a (instrSrc f)) :
    ReturnDiscards Seed Γ (.op f a) := by
  have h := primitive f hf
  have hsub : ∀ ⦃i D⦄, At [instrSrc (τ := τ) f] i D → Tm.BranchValue Γ ((fun _ : Nat => a) i) D := by
    intro i D hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact ha
    | succ i => simp [At] at hi
  exact h.substVars hsub

theorem returnDiscards_op_of_fusion {ε : Type w} [HasEff Φ ε] {pe : ε}
    (primitive : PrimitiveReturnsDiscard Seed pe) {Γ : VCtx τ} {f : Φ} {a : Tm Φ}
    (hf : IsPure pe f) (ha : Tm.HasType Γ a (instrSrc f)) (da : ReturnDiscards Seed Γ a)
    (fusion : Eqv Seed Γ (returnRegion (.op f a))
      (returnRegion (.let₁ a (.op f (.var 0)))) [instrTrg f]) :
    ReturnDiscards Seed Γ (.op f a) := by
  have inner : Tm.HasType (instrSrc f :: Γ) (.var 0 : Tm Φ) (instrSrc f) := .var rfl
  have comp := returnDiscards_let₁ Seed ha da (returnDiscards_op_branchValue Seed primitive hf (.var (i := 0) rfl))
  exact (fusion.lsubstPost (returnRegion_typed (.op ha)) (returnRegion_typed (.let₁ ha (.op inner)))
    (fun _ _ _ => .br (ℓ := 0) rfl .unit)).trans comp

set_option backward.isDefEq.respectTransparency false in
theorem returnDiscards_iff {X A : τ} {a : Tm Φ} (ha : Tm.HasType [X] a A) :
    ReturnDiscards Seed [X] a ↔
      (Paper.Extension.Singleton.projection Seed).map (Paper.TypeCategory.returnTerm ha) ≫ Paper.Extension.Singleton.discardArrow Seed A =
        Paper.Extension.Singleton.discardArrow Seed X := by
  let hr := returnRegion_typed ha
  let discardT (B : τ) : ValueBranches [B] (.br 0 (.unit : Tm Φ)) [U] := .br rfl .unit
  let hcomp := seqValueBranches hr (discardT A)
  rw [← (Paper.Extension.Singleton.projection Seed).map_comp]
  change ReturnDiscards Seed [X] a ↔
    (Paper.Extension.Singleton.projection Seed).map (Paper.TypeCategory.ofRegion hr ≫ Paper.TypeCategory.ofRegion (discardT A)) =
      Paper.Extension.Singleton.ofRegion Seed (discardT X)
  rw [Paper.TypeCategory.ofRegion_comp hr (discardT A) hcomp]
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed hcomp (discardT X)).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDiscardSyntax
