module

public import Silmaril.Semantics.Calco2019.Trace.ProfileSliding.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.ProfileSliding

/-! # Figure 4 sliding laws for the co-Cartesian guarded trace -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness.TwoBody

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D E F H J U V I : K}

/-- Sliding I has no unmarked external input or marked external output on the
second body. Its recursive input lies on its unmarked side. -/
theorem slidingI_guards (i : IsInitial I)
    (s : TwoBody P (P.sum A B) (P.sum E I) (P.sum C D) (P.sum H I) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first))
    (hu : G.nested (P.inr ≫ s.first))
    (he : G.nested (P.inl ≫ P.inl ≫ s.second)) :
    G.TraceGuard s.markedCutFirst ∧ G.TraceGuard s.markedCutSecond :=
  Proofs.Feedback.marked_cuts_guard_I i s ha hu he

/-- Sliding II has no marked external input or unmarked external output on the
second body. Its recursive output lies on its unmarked side. -/
theorem slidingII_guards (i : IsInitial I)
    (s : TwoBody P (P.sum A B) (P.sum I F) (P.sum C D) (P.sum I J) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first))
    (hu : G.nested (P.inr ≫ s.first))
    (hv : G.guarded ((P.inr ≫ s.second) ≫ externalMark)) :
    G.TraceGuard s.markedCutFirst ∧ G.TraceGuard s.markedCutSecond :=
  Proofs.Feedback.marked_cuts_guard_II i s ha hu hv

/-- Sliding III marks both recursive inputs and both recursive outputs. -/
theorem slidingIII_guards
    (s : TwoBody P (P.sum A B) (P.sum E F) (P.sum C D) (P.sum H J) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first))
    (hu : G.nested (P.inr ≫ s.first))
    (he : G.nested (P.inl ≫ P.inl ≫ s.second))
    (hv : G.nested (P.inr ≫ s.second)) :
    G.TraceGuard s.markedCutFirst ∧ G.TraceGuard s.markedCutSecond :=
  Proofs.Feedback.marked_cuts_guard_III s ha hu he hv

/-- The Conway trace validates Sliding I. -/
theorem slidingI (T : G.Conway) (i : IsInitial I)
    (s : TwoBody P (P.sum A B) (P.sum E I) (P.sum C D) (P.sum H I) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first))
    (hu : G.nested (P.inr ≫ s.first))
    (he : G.nested (P.inl ≫ P.inl ≫ s.second)) :
    T.toFixpoints.guardedTrace (s.slidingI_guards i ha hu he).1 =
      T.toFixpoints.guardedTrace (s.slidingI_guards i ha hu he).2 :=
  Proofs.Feedback.marked_slide s T hu _ _

/-- The Conway trace validates Sliding II. -/
theorem slidingII (T : G.Conway) (i : IsInitial I)
    (s : TwoBody P (P.sum A B) (P.sum I F) (P.sum C D) (P.sum I J) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first))
    (hu : G.nested (P.inr ≫ s.first))
    (hv : G.guarded ((P.inr ≫ s.second) ≫ externalMark)) :
    T.toFixpoints.guardedTrace (s.slidingII_guards i ha hu hv).1 =
      T.toFixpoints.guardedTrace (s.slidingII_guards i ha hu hv).2 :=
  Proofs.Feedback.marked_slide s T hu _ _

/-- The Conway trace validates Sliding III. -/
theorem slidingIII (T : G.Conway)
    (s : TwoBody P (P.sum A B) (P.sum E F) (P.sum C D) (P.sum H J) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first))
    (hu : G.nested (P.inr ≫ s.first))
    (he : G.nested (P.inl ≫ P.inl ≫ s.second))
    (hv : G.nested (P.inr ≫ s.second)) :
    T.toFixpoints.guardedTrace (s.slidingIII_guards ha hu he hv).1 =
      T.toFixpoints.guardedTrace (s.slidingIII_guards ha hu he hv).2 :=
  Proofs.Feedback.marked_slide s T hu _ _

end Silmaril.Calco2019.Guardedness.TwoBody
