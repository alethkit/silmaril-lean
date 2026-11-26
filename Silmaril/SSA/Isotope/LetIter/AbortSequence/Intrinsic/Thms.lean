module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Intrinsic.Defs

/-! # Equality of intrinsic LetIter classes -/

public section

namespace Silmaril.Isotope.LetIter.LocallyNameless.Intrinsic

universe u v w r

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν] {ε : Type r} [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ} {e pe : ε}
  {a b : Term Φ Γ β A e}

/-- The explicit setoid tests native abort equivalence at the endpoints. -/
theorem abortSetoid_r_iff :
    (abortSetoid pe).r a b ↔ AbortEquiv pe Γ β a.val b.val A :=
  Iff.rfl

/-- Equal classes characterize native abort equivalence of the representatives. -/
theorem abortClass_eq_iff :
    abortClass pe a = abortClass pe b ↔ AbortEquiv pe Γ β a.val b.val A :=
  ⟨Quotient.exact, @Quotient.sound _ (abortSetoid pe) a b⟩

/-- Exact native equivalence implies equality in the opt-in quotient. -/
theorem abortClass_eq_of_equiv (h : Equiv pe Γ β a.val b.val A) :
    abortClass pe a = abortClass pe b :=
  abortClass_eq_iff.mpr (.equiv h)

end Silmaril.Isotope.LetIter.LocallyNameless.Intrinsic
