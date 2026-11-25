module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.CallByValue

/-! # Derived call-by-value conversions for source expressions -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.CallByValue

universe u v w

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A B : τ} {e : ε} {a b : Expr Φ}

theorem wf_wk0 (hb : Wf Γ b B e) (slot : τ × ε) :
    Wf (slot :: Γ) b.wk0 B e :=
  Proofs.wf_wk0 hb slot

theorem op_bind {f : Φ} (hf : instrEff f ≤ e) (ha : Wf Γ a (instrSrc f) e) :
    Eqv Γ (instrTrg f) e (.op f a) (.let₁ a (.op f (.var 0))) :=
  Proofs.op_bind hf ha

theorem op_let {f : Φ} (hf : instrEff f ≤ e) (ha : Wf Γ a A e)
    (hb : Wf ((A, ⊥) :: Γ) b (instrSrc f) e) :
    Eqv Γ (instrTrg f) e (.op f (.let₁ a b)) (.let₁ a (.op f b)) :=
  Proofs.op_let hf ha hb

theorem pair_bind (ha : Wf Γ a A e) (hb : Wf Γ b B e) :
    Eqv Γ (product A B) e (.pair a b)
      (.let₁ a (.let₁ b.wk0 (.pair (.var 1) (.var 0)))) :=
  Proofs.pair_bind ha hb

theorem pair_unit_bind (ha : Wf Γ a A e) :
    Eqv Γ (product A (unit : τ)) e (.pair a .unit)
      (.let₁ a (.pair (.var 0) .unit)) :=
  Proofs.pair_unit_bind ha

theorem pair_two_bind (ha : Wf Γ a A e) (hb : Wf Γ b B e) :
    Eqv Γ (product A (product B (unit : τ))) e (.pair a (.pair b .unit))
      (.let₁ a (.let₁ b.wk0 (.pair (.var 1) (.pair (.var 0) .unit)))) :=
  Proofs.pair_two_bind ha hb

end Silmaril.Isotope.LetIter.PaperExpression.Source.CallByValue
