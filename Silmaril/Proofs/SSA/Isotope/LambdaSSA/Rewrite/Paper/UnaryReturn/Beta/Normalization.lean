module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn
open CfgEta.TypeCategory (returnRegion returnRegion_typed returnRegion_branchValue)
open Paper.TypeCategory
open BoundSimulation (boundReturn)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B D : τ} {t c : Tm Φ}
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

omit [HasTy Φ τ] in
theorem pure {ε : Type w} [HasEff Φ ε] (pe : ε) (h : BetaNormalizes Γ t c D) :
    Tm.Pure pe t := by
  induction h with
  | value hc =>
    induction hc with
    | var => exact .var
    | unit => exact .unit
    | pair _ _ ihl ihr => exact .pair ihl ihr
    | inl _ ih => exact .inl ih
    | inr _ ih => exact .inr ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb

theorem returnRegion_eq_branch (h : BetaNormalizes Γ t c D) :
    Paper.Eqv Γ (returnRegion t) (.br 0 c) [D] := by
  induction h with
  | value hc => exact .cfgEta (.native (.base (returnRegion_branchValue hc)))
  | @let₁ Γ a b c d A D ha hb ia ib =>
    have producer := returnRegion_typed ha.hasType
    have branch : ValueBranches Γ (.br 0 c) [A] := .br (ℓ := 0) rfl ha.branchValue
    have continuation : LSubst.HasType Γ [A] [D] (fun _ => .br 0 d) :=
      fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸
        (.br (ℓ := 0) rfl hb.branchValue.hasType)
    exact (Paper.lsubst_singleton_congr producer ib).trans
      (ia.lsubstPost producer branch continuation)

theorem iterate_map_uniformity (h : BetaNormalizes [A] t c D)
    (includeStep : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
    {f f₀ : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A}
    {g g₀ : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D}
    (hf : (Extension.Singleton.projection Seed).map f = (Extension.Singleton.projection Seed).map f₀)
    (hg : (Extension.Singleton.projection Seed).map g = (Extension.Singleton.projection Seed).map g₀)
    (comm : f₀ ≫ coprod.map (𝟙 (ofType B)) (returnTerm h.hasType) = returnTerm h.hasType ≫ g₀) :
    (Extension.Singleton.projection Seed).map (iterate f) =
      (Extension.Singleton.projection Seed).map (boundReturn h.hasType) ≫
        (Extension.Singleton.projection Seed).map (iterate g) := by
  have uniform := iterate_uniformity_ofReturnTerm h.hasType h.branchValue
    (returnRegion_eq_branch h) f₀ g₀ comm
  rw [Extension.Singleton.iterate_map_congr Seed hf, uniform, Functor.map_comp,
    mapped_returnTerm_eq_boundReturn includeStep h.hasType, ← Extension.Singleton.iterate_map_congr Seed hg]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta
