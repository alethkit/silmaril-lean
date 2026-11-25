module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BinaryLetBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms

/-! # The remaining Paper equation for a binary-let producer -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLetBind

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce)
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet (returnPair)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A B : τ} {Γ : VCtx τ} {a : Tm Φ}

open Paper (product_variable_eta_context)

/-- Product η closes the inner destructuring after the once-only bind. -/
theorem rebound_return (ha : Tm.HasType Γ a (Silmaril.product A B)) :
    Paper.Eqv Γ (BinaryLetBind.rebound a (.br 0 (.pair (.var 1) (.var 0)))) (returnOnce a)
      [Silmaril.product A B] := by
  let P := Silmaril.product A B
  have h : Region.HasType (P :: Γ) (.br 0 (.var 0) : Region Φ) [P] :=
    .br rfl (.var (i := 0) rfl)
  have e := product_variable_eta_context (rfl : At (P :: Γ) 0 P) h
  change Paper.Eqv (P :: Γ) (.let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0))))
    (.br 0 (.var 0)) [P] at e
  exact .let₁ ha e

/-- The exact remaining equality moves the binary destructuring across the bind. -/
theorem returnPair_iff_bind (ha : Tm.HasType Γ a (Silmaril.product A B)) :
    Paper.Eqv Γ (returnPair a) (returnOnce a) [Silmaril.product A B] ↔
      Paper.Eqv Γ (returnPair a) (BinaryLetBind.rebound a (.br 0 (.pair (.var 1) (.var 0))))
        [Silmaril.product A B] :=
  ⟨fun h => h.trans (rebound_return ha).symm, fun h => h.trans (rebound_return ha)⟩


end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLetBind
