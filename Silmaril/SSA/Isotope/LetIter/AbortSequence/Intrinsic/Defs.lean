module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms
public import Silmaril.SSA.Isotope.LetIter.Effects.Thms

/-! # An opt-in intrinsic quotient of native LetIter -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.LocallyNameless.Intrinsic

universe u v w r

variable {τ : Type u} [TypeFormers τ] (Φ : Type v) [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν] {ε : Type r} [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n) (A : τ) (e : ε)

/-- Native LetIter terms with exact type `A` and effect at most `e`, in the
fixed free context `Γ` and bound context `β`. This includes native iteration. -/
abbrev Term := {t : Tm ν Φ n // HasTypeEffect Γ β t A e}

variable {Φ Γ β A e} (pe : ε)

/-- The restriction of `AbortEquiv` to endpoints in this fiber. The independent
parameter `pe` selects pure primitives in the native equations. The effect bound
`e` constrains the endpoints of an equation, and its native proof can use
intermediates outside this fiber. -/
def abortSetoid : Setoid (Term Φ Γ β A e) where
  r a b := AbortEquiv pe Γ β a.val b.val A
  iseqv := ⟨fun a => Refinement.equiv (.refl a.prop.1), AbortEquiv.symm, Refinement.trans⟩

/-- Equivalence classes for the explicitly selected abort-sequencing setoid. -/
abbrev AbortClass := Quotient (abortSetoid (Φ := Φ) (Γ := Γ) (β := β) (A := A) (e := e) pe)

/-- Form the abort-sequencing class of an intrinsically typed endpoint. -/
def abortClass (a : Term Φ Γ β A e) : AbortClass (Φ := Φ) (Γ := Γ) (β := β) (A := A) (e := e) pe :=
  Quotient.mk _ a

end Silmaril.Isotope.LetIter.LocallyNameless.Intrinsic
