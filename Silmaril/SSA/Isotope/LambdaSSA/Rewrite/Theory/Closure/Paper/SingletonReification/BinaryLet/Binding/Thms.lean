module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BinaryLetBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLetBind

/-! # The producer premise after a once-only bind -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce)
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet (returnPair)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A B : τ} {Γ : VCtx τ} {a : Tm Φ}

/-- Product η closes the inner destructuring after the once-only bind. -/
theorem rebound_return (ha : Tm.HasType Γ a (Silmaril.product A B)) :
    Paper.Eqv Γ (BinaryLetBind.rebound a (.br 0 (.pair (.var 1) (.var 0)))) (returnOnce a)
      [Silmaril.product A B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLetBind.rebound_return ha

/-- The exact remaining equality moves the binary destructuring across the bind. -/
theorem returnPair_iff_bind (ha : Tm.HasType Γ a (Silmaril.product A B)) :
    Paper.Eqv Γ (returnPair a) (returnOnce a) [Silmaril.product A B] ↔
      Paper.Eqv Γ (returnPair a) (BinaryLetBind.rebound a (.br 0 (.pair (.var 1) (.var 0))))
        [Silmaril.product A B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLetBind.returnPair_iff_bind ha

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet
