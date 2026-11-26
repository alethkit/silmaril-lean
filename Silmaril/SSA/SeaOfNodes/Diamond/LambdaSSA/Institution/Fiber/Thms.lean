module

public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber.Adequacy

/-! Return, fault and divergence adequacy in the existing fixed-alphabet room. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber

open CategoryTheory
open RVSDG (Tuple)
open Isotope (Value)
open Isotope.Institution.Observational (Observation ssaBeh)
open Isotope.LambdaSSA.Semantics.Region (Eval)

universe u v w x
variable {Data : Type u} {P : Diamond.Institution.Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data} {σ : Type x}

/-- A room return observation is exactly execution of the emitted region
in the original input encoding, at its recorded initial and final states. -/
theorem ret_mem_eval (r : GeneratedRegion P inputs out) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) (start finish : σ)
    (label : Nat) (payload : Value (Atom m)) :
    Observation.ret start (label, payload) finish ∈ ssaBeh 1 (inputModel m σ input) (scope r) ↔
      Eval (instruction m) (inputEnv m input) r.val start label payload finish :=
  Proofs.ret_mem_eval r m input start finish label payload

/-- The room's return observations are the finite unit-state observations
with the initial state carried through unchanged. -/
theorem ret_mem_unit_eval (r : GeneratedRegion P inputs out) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) (start finish : σ)
    (label : Nat) (payload : Value (Atom m)) :
    Observation.ret start (label, payload) finish ∈ ssaBeh 1 (inputModel m σ input) (scope r) ↔
      Eval (instruction m) (inputEnv m input) r.val () label payload () ∧ finish = start :=
  Proofs.ret_mem_unit_eval r m input start finish label payload

theorem fault_absent (r : GeneratedRegion P inputs out) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) (start finish : σ) :
    Observation.fault start finish ∉ ssaBeh 1 (inputModel m σ input) (scope r) :=
  Proofs.fault_absent r m input start finish

theorem divergence_absent (r : GeneratedRegion P inputs out) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) (start : σ) :
    Observation.diverge start ∉ ssaBeh 1 (inputModel m σ input) (scope r) :=
  Proofs.divergence_absent r m input start

/-- Equality of full existing-room behaviours is equivalent to agreement of
the finite unit-state observations at this typed input. -/
theorem room_satisfaction_at [Nonempty σ] (e : Equation P) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts e.inputs)) :
    (fiberRoom.{u, v, w, x} P e.inputs.length).Sat (Discrete.mk (inputModel m σ input))
      (translateEquation e) ↔
    ∀ label payload, Eval (instruction m) (inputEnv m input) e.lhs.val () label payload () ↔
      Eval (instruction m) (inputEnv m input) e.rhs.val () label payload () :=
  Proofs.room_satisfaction_at e m input

/-- Factor the generated room's input quantification into a family of
models of the actual existing room at a single fixed scope. -/
theorem room_satisfaction (σ : Type x) [Nonempty σ] (e : Equation P) (m : Model.{u, v, w} P.op) :
    (∀ input : Tuple (Val m.value) (dataPorts e.inputs),
      (fiberRoom.{u, v, w, x} P e.inputs.length).Sat (Discrete.mk (inputModel m σ input))
        (translateEquation e)) ↔ e.Holds m :=
  forall_congr' (fun input => room_satisfaction_at (σ := σ) e m input)

/-- The original native equation holds exactly when its actual compiled
equation holds in all models induced by its typed inputs. -/
theorem translated_satisfaction (σ : Type x) [Nonempty σ]
    (e : Diamond.Institution.Equation P) (m : Model.{u, v, w} P.op) :
    (∀ input : Tuple (Val m.value) (dataPorts e.inputs),
      (fiberRoom.{u, v, w, x} P e.inputs.length).Sat (Discrete.mk (inputModel m σ input))
        (translateEquation (lowerEquation e))) ↔ e.Holds m :=
  (room_satisfaction σ (lowerEquation e) m).trans (LambdaSSA.Institution.satisfaction e m)

/-- An empty state carrier yields empty behaviours, since each observation
requires an initial state. Reflection needs an inhabited state. -/
theorem empty_state_satisfies [IsEmpty σ] (e : Equation P) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts e.inputs)) :
    (fiberRoom.{u, v, w, x} P e.inputs.length).Sat (Discrete.mk (inputModel m σ input))
      (translateEquation e) :=
  Proofs.empty_state_satisfies e m input

end Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber
