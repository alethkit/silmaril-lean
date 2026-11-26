module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Defs
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Monadic

import Silmaril.Proofs.SSA.Isotope.LetIter.Monadic.Substitution

/-! # Monadic evaluation of typed renaming and pure bound substitution -/

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics

namespace Silmaril.Isotope.LetIter.LocallyNameless.Derivation

universe u v w q

variable {τ : Type u} [TypeFormers τ] (D : τ → Type v)
  [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  {m : Type v → Type v} [Monad m] [Elgot.Iterate m] (M : InstructionModel D Φ m)
  {Γ : Ctx ν τ} {n k : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ k}
  {t : Tm ν Φ n} {A : τ} (γ : FreeEnv D Γ)

/-- Renaming preserves evaluation at matching bound valuations. -/
theorem denote_rename (d : Derivation Φ Γ β t A) (r : TypedRenaming β δ)
    (ρ : BoundEnv D β) (ξ : BoundEnv D δ) (hr : ∀ i, HEq (ξ (r.toFun i)) (ρ i)) :
    (d.rename r).denote D M γ ξ = d.denote D M γ ρ :=
  Proofs.denote_rename D M γ d r ρ ξ hr

/-- A typed substitution whose images return the old environment values
preserves evaluation of the term in that old environment. -/
theorem denote_bsubst (d : Derivation Φ Γ β t A) {σ : Fin n → Tm ν Φ k}
    (s : DerivSubst (Γ := Γ) β δ σ) (ρ : BoundEnv D β) (ξ : BoundEnv D δ)
    (hs : ∀ i, (s i).denote D M γ ξ = pure (ρ i)) :
    (d.bsubst s).denote D M γ ξ = d.denote D M γ ρ :=
  Proofs.denote_bsubst D M γ d s ρ ξ hs

end Silmaril.Isotope.LetIter.LocallyNameless.Derivation
