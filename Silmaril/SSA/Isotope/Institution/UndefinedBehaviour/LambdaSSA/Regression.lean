module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Primitive.Defs

/-! The obstruction applies to the actual dialect extension at any declared
effect. A model with both fault and primitive divergence validates the
fixed-model encoding at the empty label interface. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.Institution

namespace LambdaSSAUBRegression

local notation "DialectUB" => Silmaril.Isotope.Institution.Refinement.UB.dialect

variable {τ ε : Type} [TypeFormers τ] (P : InstrSig τ ε) (e : ε) (Γ : LambdaSSA.VCtx τ)

example :
    letI := (DialectUB P e).hasTy
    ¬ ∃ r : LambdaSSA.UB.Typed (Φ := (DialectUB P e).Instr) Γ [],
      ∀ a : LambdaSSA.UB.Typed (Φ := (DialectUB P e).Instr) Γ [],
        LambdaSSA.UB.Refines.{0,0,0,0} a r :=
  letI := (DialectUB P e).hasTy
  LambdaSSA.UB.no_greatest Γ [] (Sum.inr (unit : τ) : (DialectUB P e).Instr) rfl

private def saturated {Φ : Type} {n : Nat} : Model.{0,0,0} Φ n where
  α := Unit
  σ := Unit
  instr _ _ _ _ _ := False
  faults _ _ _ _ := True
  prim _ _ _ := True
  bound _ := .unit

example :
    letI := (DialectUB P e).hasTy
    LambdaSSA.UB.observe saturated
        (LambdaSSA.UB.primitiveThenLoop Γ [] (Sum.inr (unit : τ) : (DialectUB P e).Instr) rfl) =
      LambdaSSA.UB.emptyObservations Unit Unit :=
  letI := (DialectUB P e).hasTy
  LambdaSSA.UB.observe_primitiveThenLoop_eq_empty saturated
    (Sum.inr (unit : τ) : (DialectUB P e).Instr) rfl
    (fun _ _ => trivial) (fun _ => Or.inl trivial)

#print axioms LambdaSSA.UB.not_noLocalBlocks
#print axioms LambdaSSA.UB.no_greatest
#print axioms LambdaSSA.UB.observe_primitiveThenLoop_eq_empty

end LambdaSSAUBRegression
