module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.MatrixTrace.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.CounterSemiringMatrixTrace

/-! # The total matrix trace and its Conway operator -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.CounterSemiring.FiniteMatrix

open Guardedness

/-- Feedback elimination satisfies the ordinary trace equations on all finite matrices. -/
theorem traceLaws : Feedback.JoyalStreetVerity feedback.{u} where
  tighten f a b h := Proofs.CounterSemiringMatrixTrace.tighten_eq f a b h
  superpose f g h := Proofs.CounterSemiringMatrixTrace.superpose_eq f g h
  slide f q := Proofs.CounterSemiringMatrixTrace.slide_eq f q
  vanishInitial i f := Proofs.CounterSemiringMatrixTrace.vanish_initial_eq i f
  vanishPair s := Proofs.CounterSemiringMatrixTrace.vanish_pair_eq s
  yank U := Proofs.CounterSemiringMatrixTrace.yank_eq U

/-- The total Conway operator induced by the matrix trace. -/
noncomputable def conway : (Guardedness.greatest (coproducts : Coproducts Object.{u})).Conway :=
  Feedback.conway (traceLaws.lawful)

end Silmaril.Calco2019.CounterSemiring.FiniteMatrix
