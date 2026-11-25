module

public import Silmaril.Semantics.Calco2019.Trace.Profile.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Profile

/-! # Four-interface guard normalization and tightening -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- The normalization preserves both marked guards and is invertible. -/
def profileEquiv (G : Guardedness P) (A B C D U : K) :
    {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U) // G.TraceGuard f} ≃
    {f : P.sum (P.sum A B) U ⟶ P.sum (P.sum C D) U // G.ProfileGuard f} where
  toFun f := ⟨traceBody f.val, by exact (Proofs.Feedback.profile_guard f.val).1 f.property⟩
  invFun f := ⟨restoreTraceBody f.val, by exact (Proofs.Feedback.restore_guard_iff f.val).2 f.property⟩
  left_inv f := Subtype.ext (Proofs.Feedback.restore_traceBody f.val)
  right_inv f := Subtype.ext (Proofs.Feedback.traceBody_restore f.val)

variable {A B C D U A' B' C' D' : K}
  {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
  (a : P.sum A' B' ⟶ P.sum A B) (b : P.sum C D ⟶ P.sum C' D')

/-- Guarded maps on the external interfaces preserve the four-interface guard. -/
theorem traceTighten_guard (hf : G.TraceGuard f)
    (ha : G.guarded (P.inl ≫ a)) (hb : G.guarded (P.inl ≫ b)) :
    G.TraceGuard (traceTighten f a b) :=
  Proofs.Feedback.profile_tightening_guard a b hf ha hb

/-- Tightening commutes with the four-interface trace. The external maps may
move between the summands subject to the indicated guards. -/
theorem guardedTrace_tighten (F : G.Conway) (hf : G.TraceGuard f)
    (ha : G.guarded (P.inl ≫ a)) (hb : G.guarded (P.inl ≫ b)) :
    F.toFixpoints.guardedTrace (traceTighten_guard a b hf ha hb) =
      a ≫ F.toFixpoints.guardedTrace hf ≫ b :=
  Proofs.Feedback.profile_tightening F a b hf (traceTighten_guard a b hf ha hb)

end Silmaril.Calco2019.Guardedness
