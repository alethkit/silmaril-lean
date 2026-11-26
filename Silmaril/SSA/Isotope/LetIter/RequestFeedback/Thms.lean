module

public import Silmaril.SSA.Isotope.LetIter.RequestFeedback.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.RequestFeedback.Padding

/-! # Removing a redundant field from a request feedback loop -/

public section

open Silmaril Silmaril.Isotope

namespace Silmaril.Isotope.LetIter.LocallyNameless.RequestFeedback

universe u v w r

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν] {ε : Type r} [HasEff Φ ε]
  {n : Nat} {Γ : Ctx ν τ} {β : BoundCtx τ n} {f : Φ}
  {init : Tm ν Φ n} {R : τ} {pe : ε}

/-- Pure uniformity removes the appended unit and leaves the sum-returning
request as the loop body. The right reply still sets the next state. -/
theorem remove_unit (hout : instrTrg f = coprod R (instrSrc f))
    (ha : HasType Φ Γ β init (instrSrc f)) :
    Equiv pe Γ β (padded f init) (loop f init) R :=
  Proofs.remove_unit hout ha

omit [DecidableEq ν] in
/-- Pure state padding leaves the inferred effect of the entire loop equal. -/
theorem effect_eq [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
    (f : Φ) (init : Tm ν Φ n) : (padded f init).effect = ((loop f init).effect : ε) :=
  Proofs.effect_eq (ε := ε) f init

/-- Remove the unit field at any bound already admitted by the loop. -/
theorem remove_unit_at_bound [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}
    (hout : instrTrg f = coprod R (instrSrc f))
    (ha : HasType Φ Γ β init (instrSrc f)) (he : HasEffect (loop f init) e) :
    HasTypeEffect Γ β (padded f init) R e ∧ HasTypeEffect Γ β (loop f init) R e ∧
      Equiv (⊥ : ε) Γ β (padded f init) (loop f init) R :=
  Proofs.remove_unit_at_bound hout ha he

end Silmaril.Isotope.LetIter.LocallyNameless.RequestFeedback
