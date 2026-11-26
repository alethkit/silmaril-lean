module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms

/-! # Input records and contextual η in the joined quotient -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedInputPacking

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.InputDestructure
open Silmaril.DeBruijn (lift lift_comp lift_id)
open Paper.WithProjectionReturnsAndUnitEta (Step)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
local notation "E" => Paper.Extension.Eqv (Step (τ := τ) (Φ := Φ))

private def rebuiltValue (Γ : VCtx τ) : Tm Φ :=
  (packedInputValue Γ).rename (field Γ)

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem rebuiltValue_cons (A : τ) (Γ : VCtx τ) :
    (rebuiltValue (Φ := Φ) (A :: Γ)) =
      .pair (rebuiltValue Γ) (.var (retained Γ 0)) := by
  simp only [rebuiltValue, packedInputValue, Tm.rename, Tm.rename_comp]
  rfl

private def rebuild (Γ : VCtx τ) (i : Nat) : Region Φ :=
  split Γ i (.br 0 (rebuiltValue Γ))

private theorem rebuild_typed (Γ : VCtx τ) {Δ : VCtx τ} {i : Nat}
    (hi : At Δ i (packedInputType Γ)) : ValueBranches Δ (rebuild (Φ := Φ) Γ i) [packedInputType Γ] := by
  have value := (packedInputValue_branchValue (Φ := Φ) Γ).subst (σ := Tm.var ∘ field Γ)
    (fun _ _ h => .var (fieldRen Γ Δ h))
  rw [← Tm.rename_eq_subst] at value
  exact split_valueBranches Γ hi (.br rfl value)

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem split_lsubst (Γ : VCtx τ) (i : Nat) (r : Region Φ) (σ : Nat → Region Φ) :
    (split Γ i r).lsubst σ =
      split Γ i (r.lsubst (fun j => (σ j).renameVars (lift (retained Γ)))) := by
  induction Γ generalizing i r σ with
  | nil =>
    change r.lsubst σ = r.lsubst (fun j => (σ j).renameVars (lift id))
    simp only [lift_id, renameVars_id]
  | cons A Γ ih =>
    simp only [split, lsubst, ih, liftLSubstVars, renameVars_comp, ← lift_comp]
    rfl

private theorem unit_eta {Δ : VCtx τ} {i : Nat} (hi : At Δ i (Silmaril.unit : τ)) :
    E Δ (.br 0 .unit) (.br 0 (.var i)) [Silmaril.unit] := by
  have seed : E [(Silmaril.unit : τ)] (.br 0 .unit) (.br 0 (.var 0)) [Silmaril.unit] :=
    .extra (.br rfl .unit) (.br rfl (.var rfl)) (Or.inr .unit)
  apply seed.substVars (θ := fun _ => .var i)
  intro j B hj
  cases j with
  | zero => cases Option.some.inj hj; exact .var hi
  | succ j => simp [At] at hj

private theorem rebuild_eta (Γ : VCtx τ) {Δ : VCtx τ} {i : Nat}
    (hi : At Δ i (packedInputType Γ)) :
    E Δ (rebuild Γ i) (.br 0 (.var i)) [packedInputType Γ] := by
  induction Γ generalizing Δ i with
  | nil => exact unit_eta hi
  | cons A Γ ih =>
    let tail := packedInputType Γ
    let tailAt : At (A :: tail :: Δ) 1 tail := rfl
    let pairBranch : Region Φ := .br 0 (.pair (.var 0) (.var 1))
    have h : LSubst.HasType (A :: tail :: Δ) [tail] [Silmaril.product tail A] (fun _ => pairBranch) := by
      intro j B hj
      cases j with
      | zero =>
        cases Option.some.inj hj
        exact .br rfl (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))
      | succ j => simp [At] at hj
    have e := (ih tailAt).lsubstPost (rebuild_typed Γ tailAt) (.br (rfl : At [tail] 0 tail) (.var tailAt)) h
    have left :
        (rebuild Γ 1).lsubst (fun _ => pairBranch) =
          split Γ 1 (.br 0 (.pair (rebuiltValue Γ) (.var (retained Γ 0)))) := by
      unfold rebuild
      rw [split_lsubst]
      rfl
    rw [left] at e
    have step : E Δ (rebuild (A :: Γ) i)
        (.let₂ (.var i) (.br 0 (.pair (.var 1) (.var 0)))) [Silmaril.product tail A] := by
      unfold rebuild
      rw [rebuiltValue_cons]
      exact .let₂ (.var hi) e
    exact step.trans (.paper (.productEta (.let₂Eta hi rfl)))

theorem repack_unpack {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : HasType [packedInputType Γ] r L) :
    E [packedInputType Γ] ((r.unpackInputs Γ).packInputsDestructure Γ) r L := by
  let P := packedInputType Γ
  have typed : HasType (P :: [P]) r L := by
    have ren : Ren [P] (P :: [P]) id := by
      intro i A hi
      cases i with
      | zero => exact hi
      | succ i => simp [At] at hi
    simpa only [renameVars_id] using hr.renameVars ren
  have k : LSubst.HasType [P] [P] L (fun _ => r) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact typed
    | succ i => simp [At] at hi
  have e := (rebuild_eta Γ (Δ := [P]) (rfl : At [P] 0 P)).lsubstPost
    (rebuild_typed Γ (Δ := [P]) (rfl : At [P] 0 P)) (.br rfl (.var rfl)) k
  have fixed (ρ : Nat → Nat) : r.renameVars (lift ρ) = r := by
    rw [renameVars_eq_substVars]
    exact hr.substVars_singleton_fixed rfl
  have packed :
      (rebuild Γ 0).lsubst (fun _ => r) = (r.unpackInputs Γ).packInputsDestructure Γ := by
    unfold rebuild packInputsDestructure unpackInputs
    rw [split_lsubst]
    simp only [lsubst, fixed]
    apply congrArg (split Γ 0)
    conv_lhs => rw [← fixed (field Γ)]
    rw [substVars_renameVars, renameVars_substVars]
    congr 1
    funext i
    cases i <;> rfl
  have direct : (Region.br 0 (.var 0)).lsubst (fun _ => r) = r := by
    change r.substVars (Tm.singleSubst (.var 0)) = r
    exact hr.substVars_singleton_fixed rfl
  rw [packed, direct] at e
  exact e

omit [HasTy Φ τ] in
private theorem unpack_valueSubst (Γ : VCtx τ) ⦃i : Nat⦄ ⦃A : τ⦄
    (hi : At [packedInputType Γ] i A) :
    Tm.BranchValue Γ ((Tm.singleSubst (packedInputValue Γ : Tm Φ)) i) A := by
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact packedInputValue_branchValue Γ
  | succ i => simp [At] at hi

theorem unpack_valueBranches {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches [packedInputType Γ] r L) : ValueBranches Γ (r.unpackInputs Γ) L :=
  hr.substVars (unpack_valueSubst Γ)

theorem unpack_congr {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : E [packedInputType Γ] r s L) : E Γ (r.unpackInputs Γ) (s.unpackInputs Γ) L :=
  h.substVars (unpack_valueSubst Γ)

private theorem split_congr (Γ : VCtx τ) {Δ : VCtx τ} {i : Nat} {r s : Region Φ}
    {L : LCtx τ} (hi : At Δ i (packedInputType Γ)) (h : E (expanded Γ Δ) r s L) :
    E Δ (split Γ i r) (split Γ i s) L := by
  induction Γ generalizing Δ i with
  | nil => exact h
  | cons A Γ ih => exact .let₂ (.var hi) (ih (i := 1) rfl h)

theorem pack_congr {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : E Γ r s L) : E [packedInputType Γ] (r.packInputsDestructure Γ) (s.packInputsDestructure Γ) L :=
  split_congr Γ rfl (h.renameVars (fieldRen Γ [packedInputType Γ]))

private theorem of_productBeta {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : ProductBeta.Eqv Γ r s L) : Paper.Eqv Γ r s L := by
  have one {a b : Region Φ} : CfgEta.Eqv Γ a b L ∨ ProductBeta.Step Γ a b L → Paper.Eqv Γ a b L :=
    fun h => h.elim Paper.Eqv.cfgEta Paper.Eqv.productBeta
  have step {a b : Region Φ} :
      Relation.SymmGen (fun p q => CfgEta.Eqv Γ p q L ∨ ProductBeta.Step Γ p q L) a b →
        Paper.Eqv Γ a b L :=
    fun h => h.elim one (fun h => (one h).symm)
  induction h with
  | single h => exact step h
  | tail _ h ih => exact ih.trans (step h)

theorem unpack_pack {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : HasType Γ r L) : E Γ ((r.packInputsDestructure Γ).unpackInputs Γ) r L :=
  .paper (of_productBeta hr.unpack_packInputsDestructure)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedInputPacking
