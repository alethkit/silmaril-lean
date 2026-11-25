module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs

/-! # Packed inputs and a guarded producer for binary let -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region

universe u v

/-- Supply a right-associated record of the retained input and the two components. -/
def applyPackedPair {Φ : Type v} (p : Region Φ) : Region Φ :=
  p.substVars (Tm.consSubst (.pair (.var 2) (.pair (.var 1) (.var 0)))
    (Tm.var ∘ (Nat.succ ∘ Nat.succ ∘ Nat.succ)))

/-- Evaluate a product scrutinee once and return the rebuilt product. -/
def returnPair {Φ : Type v} (a : Tm Φ) : Region Φ :=
  .let₂ a (.br 0 (.pair (.var 1) (.var 0)))

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B : τ} {a : Tm Φ}

theorem returnPair_typed (ha : Tm.HasType [X] a (Silmaril.product A B)) :
    ValueBranches [X] (returnPair a) [Silmaril.product A B] :=
  .let₂ ha (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet
