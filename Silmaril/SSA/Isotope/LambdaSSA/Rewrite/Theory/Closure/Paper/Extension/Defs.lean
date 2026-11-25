module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs

/-! # Contextual extensions of the Paper rewrite relation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A typed contextual closure of the existing Paper equations and an
additional relation. The seed constructor checks both endpoints at a common
interface. Region contexts and the guarded substitutions of the Paper
presentation transport new equations. -/
inductive Eqv (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) :
    VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | paper : Paper.Eqv Γ r s L → Eqv Seed Γ r s L
  | extra (hr : HasType Γ r L) (hs : HasType Γ s L) : Seed Γ r s L → Eqv Seed Γ r s L
  | symm : Eqv Seed Γ r s L → Eqv Seed Γ s r L
  | trans : Eqv Seed Γ r s L → Eqv Seed Γ s t L → Eqv Seed Γ r t L
  | let₁ (ha : Tm.HasType Γ a A) (hr : Eqv Seed (A :: Γ) r s L) :
      Eqv Seed Γ (.let₁ a r) (.let₁ a s) L
  | let₂ (ha : Tm.HasType Γ a (Silmaril.product A B)) (hr : Eqv Seed (B :: A :: Γ) r s L) :
      Eqv Seed Γ (.let₂ a r) (.let₂ a s) L
  | case (ha : Tm.HasType Γ a (Silmaril.coprod A B))
      (hl : Eqv Seed (A :: Γ) l l' L) (hr : Eqv Seed (B :: Γ) r r' L) :
      Eqv Seed Γ (.case a l r) (.case a l' r') L
  | cfg (R : Fin n → τ) (he : Eqv Seed Γ entry entry' (List.ofFn R ++ L))
      (hb : ∀ i, Eqv Seed (R i :: Γ) (bs i) (bs' i) (List.ofFn R ++ L)) :
      Eqv Seed Γ (.cfg entry n bs) (.cfg entry' n bs') L
  | lsubstCongr (hp : ValueBranches Γ p L)
      (h : ∀ ⦃i A⦄, At L i A → Eqv Seed (A :: Γ) (σ i) (υ i) K) :
      Eqv Seed Γ (p.lsubst σ) (p.lsubst υ) K
  | lsubstPost (h : Eqv Seed Γ r s L) (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L)
      (hσ : LSubst.HasType Γ L K σ) :
      Eqv Seed Γ (r.lsubst σ) (s.lsubst σ) K
  | substVars (h : Eqv Seed Γ r s L)
      (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
      Eqv Seed Δ (r.substVars θ) (s.substVars θ) L
  | renameLabels (h : Eqv Seed Γ r s L) (hρ : Ren L K ρ) :
      Eqv Seed Γ (r.renameLabels ρ) (s.renameLabels ρ) K

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension
