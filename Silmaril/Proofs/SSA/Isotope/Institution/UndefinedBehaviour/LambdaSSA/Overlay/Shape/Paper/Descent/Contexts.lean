module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Literal
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.ValueRules
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Preservation

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape (EnvTyped ValueTyped)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation
  (Ops RegionAt PureValue Realizes ShapedObs branchValue_pure_typed)
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {α : Type w} {σ : Type x}
  {Γ Δ L : List (Ty κ)} {r t : Region Φ}

local notation "Obs" => ShapedObs (Φ := Φ) (κ := κ) (α := α) (σ := σ)

theorem lsubstPost (hr : ValueBranches Γ r L) (ht : ValueBranches Γ t L) (h : Obs Γ r t)
    (k : Nat → Region Φ) : Obs Γ (r.lsubst k) (t.lsubst k) := by
  intro O types steps env shaped
  apply regionAt_iff.mpr
  intro s o
  rw [literal hr k s o, literal ht k s o]
  exact exists_congr fun e => and_congr_left' (regionAt_iff.mp (h O types steps env shaped) s e)

theorem lsubstCongr (hr : ValueBranches Γ r L) {k j : Nat → Region Φ}
    (h : ∀ ⦃i A⦄, At L i A → Obs (A :: Γ) (k i) (j i)) :
    Obs Γ (r.lsubst k) (r.lsubst j) := by
  intro O types steps env shaped
  apply regionAt_iff.mpr
  intro s o
  rw [literal hr k s o, literal hr j s o]
  apply exists_congr
  intro e
  apply and_congr_right
  intro run
  cases e with
  | ret i a t =>
    obtain ⟨A, label, typed⟩ := region_eval_typed_at steps shaped hr.hasType run
    exact regionAt_iff.mp (h label O types steps _ (shaped.extend typed)) t o
  | fault | diverge => rfl

theorem renameLabels (h : Obs Γ r t) (ρ : Nat → Nat) :
    Obs Γ (r.renameLabels ρ) (t.renameLabels ρ) := by
  intro O types steps env shaped
  apply regionAt_iff.mpr
  intro s o
  rw [runs_renameLabels, runs_renameLabels]
  exact exists_congr fun _ => and_congr_right' (regionAt_iff.mp (h O types steps env shaped) s _)

private abbrev Agree {τ : Type v} (Γ : List τ) (θ φ : Nat → Tm Φ) : Prop :=
  ∀ ⦃i A⦄, At Γ i A → θ i = φ i

private theorem Agree.lift {τ : Type v} {Γ : List τ} {θ φ : Nat → Tm Φ}
    (h : Agree Γ θ φ) (A : τ) : Agree (A :: Γ) (Tm.liftSubst θ) (Tm.liftSubst φ) := by
  intro i B hi
  cases i with
  | zero => rfl
  | succ i => exact congrArg (fun t => t.rename Nat.succ) (h (show At Γ i B from hi))

private theorem term_subst_agree {a : Tm Φ} {A : Ty κ} (ha : a.HasType Γ A)
    {θ φ : Nat → Tm Φ} (agree : Agree Γ θ φ) : a.subst θ = a.subst φ := by
  induction ha generalizing θ φ with
  | var h => exact agree h
  | unit => rfl
  | op _ ih => simp only [Tm.subst, ih agree]
  | pair _ _ il ir => simp only [Tm.subst, il agree, ir agree]
  | inl _ ih | inr _ ih | abort _ ih => simp only [Tm.subst, ih agree]
  | let₁ _ _ il ir => simp only [Tm.subst, il agree, ir (agree.lift _)]
  | let₂ _ _ il ir => simp only [Tm.subst, Tm.liftSubstN, il agree, ir ((agree.lift _).lift _)]
  | case _ _ _ i ih₁ ih₂ => simp only [Tm.subst, i agree, ih₁ (agree.lift _), ih₂ (agree.lift _)]

private theorem region_subst_agree (hr : r.HasType Γ L) {θ φ : Nat → Tm Φ} (agree : Agree Γ θ φ) :
    r.substVars θ = r.substVars φ := by
  induction hr generalizing θ φ with
  | br _ ha => simp only [Region.substVars, term_subst_agree ha agree]
  | let₁ ha _ ih => simp only [Region.substVars, term_subst_agree ha agree, ih (agree.lift _)]
  | let₂ ha _ ih => simp only [Region.substVars, Tm.liftSubstN, term_subst_agree ha agree, ih ((agree.lift _).lift _)]
  | case ha _ _ il ir =>
    simp only [Region.substVars, term_subst_agree ha agree, il (agree.lift _), ir (agree.lift _)]
  | cfg R _ _ ie ib =>
    exact congrArg₂ (fun entry blocks => Region.cfg entry _ blocks)
      (ie agree) (funext fun i => ib i (agree.lift (R i)))

/-- Only in-scope substitution images need to be constructor values. Extend
the finite realization with a fixed pure term before applying substitution. -/
theorem substVars (hr : r.HasType Γ L) (ht : t.HasType Γ L) (h : Obs Γ r t)
    {θ : Nat → Tm Φ} (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    Obs Δ (r.substVars θ) (t.substVars θ) := by
  classical
  intro O types steps env shaped
  let φ (i : Nat) := if i < Γ.length then θ i else Tm.unit
  have agree : Agree Γ θ φ := by
    intro i A hi
    exact (ite_eq_left (List.getElem?_eq_some_iff.mp hi).choose).symm
  have value (i : Nat) : ∃ v, PureValue O env (φ i) v ∧
      ∀ A, At Γ i A → ValueTyped types v A := by
    by_cases hi : i < Γ.length
    · rw [show φ i = θ i from ite_eq_left hi]
      have slot : At Γ i (Γ[i]) := List.getElem?_eq_getElem hi
      obtain ⟨v, pure, typed⟩ := branchValue_pure_typed (O := O) (hθ slot) shaped
      exact ⟨v, pure, fun _ hA => (Option.some.inj (slot.symm.trans hA)) ▸ typed⟩
    · rw [show φ i = .unit from ite_eq_right hi]
      exact ⟨.unit, PureValue.unit, fun _ hA => (hi (List.getElem?_eq_some_iff.mp hA).choose).elim⟩
  let inner (i : Nat) := (value i).choose
  have realize : Realizes O env φ inner := fun i => (value i).choose_spec.1
  have innerTyped : EnvTyped types Γ inner := fun _ _ hi => (value _).choose_spec.2 _ hi
  rw [region_subst_agree hr agree, region_subst_agree ht agree]
  exact (realize.region r).trans ((h O types steps inner innerTyped).trans (realize.region t).symm)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent
