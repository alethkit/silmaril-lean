module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ProductEta.Step.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Preservation

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L : List (Ty κ)}
  {r t : LambdaSSA.Region Φ}

omit [HasTy Φ (Ty κ)] in
private theorem branchValue_inhabits {a : Tm Φ} {A : Ty κ} (h : a.BranchValue Γ A)
    {α : Type w} {atomType : α → κ → Prop} {env : Env α} (typed : EnvTyped atomType Γ env) :
    ∃ b, ValueTyped atomType b A := by
  induction h with
  | var atSlot => exact ⟨_, typed atSlot⟩
  | unit => exact ⟨_, .unit⟩
  | pair _ _ left right =>
      obtain ⟨_, left⟩ := left
      obtain ⟨_, right⟩ := right
      exact ⟨_, .pair left right⟩
  | inl _ ih =>
      obtain ⟨_, run⟩ := ih
      exact ⟨_, .inl run⟩
  | inr _ ih =>
      obtain ⟨_, run⟩ := ih
      exact ⟨_, .inr run⟩

theorem no_model_of_empty_branchValue {a : Tm Φ} (ha : a.BranchValue Γ (.empty : Ty κ))
    (M : Shape.Model.{u,v,w,x} Φ Γ) : False := by
  obtain ⟨_, shape⟩ := branchValue_inhabits ha (env_typed M)
  cases shape

private theorem var_result {α : Type w} {σ : Type x}
    {instr : Φ → Value α → σ → Value α → σ → Prop} {env : Env α}
    {i : Nat} {s t : σ} {v : Value α}
    (run : Semantics.Tm.Eval instr env (.var i) s v t) : t = s ∧ env i = v := by
  cases run
  exact ⟨rfl, rfl⟩

private theorem split_rebuild {α : Type w} {σ : Type x}
    {instr : Φ → Value α → σ → Value α → σ → Prop} {env : Env α}
    {i ℓ j : Nat} {s t : σ} {out a b : Value α} (pair : env i = .pair a b) :
    Semantics.Region.Eval instr env (.let₂ (.var i) (.br ℓ (.pair (.var 1) (.var 0)))) s j out t ↔
      Semantics.Region.Eval instr env (.br ℓ (.var i)) s j out t := by
  constructor
  · rintro run
    cases run with
    | let₂ arg body =>
      obtain ⟨rfl, same⟩ := var_result arg
      cases body with
      | br arg =>
        cases arg with
        | pair left right =>
          cases left
          cases right
          exact .br (.var_of_eq same)
  · rintro run
    cases run with
    | br arg =>
      cases arg
      rw [pair]
      exact .let₂ (.var_of_eq pair) (.br (.pair .var .var))

theorem product_eta (h : LambdaSSA.Region.ProductEta.Step Γ r t L)
    (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    Shape.denote (.native ⟨r, h.typed.1⟩) M s = Shape.denote (.native ⟨t, h.typed.2⟩) M s := by
  cases h with
  | @let₂Eta _ i ℓ A B hi hℓ =>
    have value := env_typed M hi
    generalize e : envOfBound M.raw.bound i = p at value
    cases value with
    | pair a b =>
      simp only [Shape.denote, UB.Overlay.denote, WithTop.coe_inj]
      apply Set.ext
      intro o
      simp only [mem_nativeOutcomes_iff _ (envOfBound_agrees M.raw.bound)]
      cases o with
      | ret j a t => exact split_rebuild e
      | fault t =>
        constructor
        · intro fault
          cases fault with
          | let₂_arg arg => cases arg
          | let₂_body _ body =>
            cases body with
            | br arg =>
              cases arg with
              | pair_left left => cases left
              | pair_right _ right => cases right
        · intro fault
          cases fault with
          | br arg => cases arg
      | diverge =>
        constructor
        · intro div
          cases div.unfold with
          | let₂_arg arg => cases arg
          | core core =>
            cases core with
            | let₂ _ body =>
              cases body.unfold with
              | core core => cases core
              | br arg =>
                cases arg with
                | pair_left left => cases left
                | pair_right _ right => cases right
        · intro div
          cases div.unfold with
          | core core => cases core
          | br arg => cases arg

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape
