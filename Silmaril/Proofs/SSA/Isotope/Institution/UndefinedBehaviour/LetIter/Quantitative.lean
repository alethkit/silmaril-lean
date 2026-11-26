module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Quantitative.Defs

public section

namespace Silmaril.Proofs.Isotope.Refinement.UB

open Silmaril.Isotope
open Silmaril.Isotope.Refinement
open Silmaril.Isotope.Refinement.UB
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Refinement.UB (dialect dialectTyping)
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)

attribute [local instance] dialectTyping

universe u

variable {τ ε : Type u} [TypeFormers τ] [TypeQuantity τ] [EffectSystem ε]
variable {P : InstrSig τ ε} {e bound : ε} {n : Nat} {Γ : QCtx τ n} {A : τ}

theorem literal_typing_iff :
    Nonempty (Typed P e Γ bound (literal P e A) A) ↔ Γ.Discardable ∧ e ≤ bound := by
  constructor
  · rintro ⟨h⟩
    cases h with
    | op he h =>
      cases h with
      | unit hd => exact ⟨hd, he⟩
  · exact fun ⟨hd, he⟩ => ⟨typeLiteral hd he⟩

theorem bound_state_discardable {Γ : QCtx τ n} {A : τ} (h : Γ.linearity = ⊤) :
    (Γ.snoc A).Discardable ↔ Quantity.affine ≤ quantity A := by
  rw [QCtx.discardable_iff_linearity, QCtx.linearity_snoc, h,
    inf_top_eq, Usage.linearity_used, inf_top_eq]

theorem relation_rename (P : InstrSig τ ε) (e : ε) :
    Relation.RenamingClosed (topRelation P e) := by
  let := (dialect P e).hasEff
  intro n m Γ Θ a b A ρ hw
  rintro ⟨rfl, ha, hb⟩
  exact ⟨rfl, WellTyped.rename ha hw, WellTyped.rename hb hw⟩

theorem relation_subst (P : InstrSig τ ε) (e : ε) :
    letI := (dialect P e).hasEff
    Relation.PureSubstitutionClosed (ε := ε) .iter (topRelation P e) := by
  let := (dialect P e).hasEff
  intro n m Δ Γ a b A σ hσ
  rintro ⟨rfl, ha, hb⟩
  have hs : Substitution.Admissible .iter Γ (⊥ : ε) σ Δ :=
    ⟨Δ, QCtx.Weakening.refl Δ, ⟨hσ⟩⟩
  exact ⟨rfl, WellTyped.bsubstAdmissible ha hs, WellTyped.bsubstAdmissible hb hs⟩

end Silmaril.Proofs.Isotope.Refinement.UB
