module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBinaryLetBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Binding.Thms

/-! # Rebuilding the bound product in the extended relation -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBinaryLetBind

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind (Eqv let₂_bind)
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet (returnPair rebound_return)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {a : Tm Φ} {A B : τ}

theorem returnPair_eq_returnOnce (ha : Tm.HasType Γ a (product A B)) :
    Eqv Γ (returnPair a) (returnOnce a) [product A B] := by
  have h := let₂_bind ha (.br (rfl : At [product A B] 0 (product A B))
    (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))
  exact h.trans (.paper (rebound_return ha))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBinaryLetBind
