module

public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber.Proofs

open CategoryTheory
open RVSDG (Tuple)
open Isotope (Value)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open Isotope.Institution.Observational
  (Observation ssaBeh ret_mem_ssaBeh fault_mem_ssaBeh diverge_mem_ssaBeh scoped_eval_congr)
open Isotope.Morphism.SSAIter (envOfBound_agrees)

universe u v w x
variable {Data : Type u} {P : Diamond.Institution.Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data} {σ : Type x}

theorem ret_mem_eval (r : GeneratedRegion P inputs out) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) (start finish : σ)
    (label : Nat) (payload : Value (Atom m)) :
    Observation.ret start (label, payload) finish ∈ ssaBeh 1 (inputModel m σ input) (scope r) ↔
      Eval (instruction m) (inputEnv m input) r.val start label payload finish :=
  ret_mem_ssaBeh.trans (scoped_eval_congr (scope r).property
    (envOfBound_agrees (inputModel m σ input).bound) (fun _ => rfl))

theorem fault_absent (r : GeneratedRegion P inputs out) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) (start finish : σ) :
    Observation.fault start finish ∉ ssaBeh 1 (inputModel m σ input) (scope r) :=
  fun member => (fault_mem_ssaBeh.mp member).false

theorem divergence_absent (r : GeneratedRegion P inputs out) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) (start : σ) :
    Observation.diverge start ∉ ssaBeh 1 (inputModel m σ input) (scope r) := by
  intro member
  obtain ⟨_, g, eq⟩ := r.property
  let payload := encode m (g.denote m input)
  have run : Eval (instruction m) (inputEnv m input) r.val start 0 payload start :=
    eq ▸ (lower_eval_iff g m input start start 0 payload).2 ⟨rfl, rfl, rfl⟩
  have observed := (ret_mem_eval r m input start start 0 payload).2 run
  exact (ret_mem_ssaBeh.mp observed).not_diverges (instruction_deterministic m)
    (Isotope.LambdaSSA.Semantics.External.Diverges.false_iff.mp (diverge_mem_ssaBeh.mp member))

theorem ret_mem_unit_eval (r : GeneratedRegion P inputs out) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) (start finish : σ)
    (label : Nat) (payload : Value (Atom m)) :
    Observation.ret start (label, payload) finish ∈ ssaBeh 1 (inputModel m σ input) (scope r) ↔
      Eval (instruction m) (inputEnv m input) r.val () label payload () ∧ finish = start := by
  refine (ret_mem_eval r m input start finish label payload).trans ?_
  obtain ⟨_, g, eq⟩ := r.property
  rw [← eq]
  refine (lower_eval_iff g m input start finish label payload).trans ?_
  have unit := lower_eval_iff g m input () () label payload
  exact ⟨fun ⟨exit, result, state⟩ => ⟨unit.2 ⟨exit, result, rfl⟩, state⟩,
    fun ⟨run, state⟩ => ⟨(unit.1 run).1, (unit.1 run).2.1, state⟩⟩

theorem room_satisfaction_at [Nonempty σ] (e : Equation P) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts e.inputs)) :
    (fiberRoom.{u, v, w, x} P e.inputs.length).Sat (Discrete.mk (inputModel m σ input))
      (translateEquation e) ↔
    ∀ label payload, Eval (instruction m) (inputEnv m input) e.lhs.val () label payload () ↔
      Eval (instruction m) (inputEnv m input) e.rhs.val () label payload () := by
  change ssaBeh 1 (inputModel m σ input) (scope e.lhs) =
    ssaBeh 1 (inputModel m σ input) (scope e.rhs) ↔ _
  constructor
  · intro equal label payload
    obtain ⟨state⟩ := ‹Nonempty σ›
    have lhs := ret_mem_unit_eval e.lhs m input state state label payload
    have rhs := ret_mem_unit_eval e.rhs m input state state label payload
    exact ⟨fun run => (rhs.1 (equal ▸ lhs.2 ⟨run, rfl⟩)).1,
      fun run => (lhs.1 (equal.symm ▸ rhs.2 ⟨run, rfl⟩)).1⟩
  · intro finite
    apply Observation.set_eq_iff.mpr
    refine ⟨?_, fun s t => iff_of_false (fault_absent e.lhs m input s t)
      (fault_absent e.rhs m input s t), fun s => iff_of_false
        (divergence_absent e.lhs m input s) (divergence_absent e.rhs m input s)⟩
    rintro start ⟨label, payload⟩ finish
    exact (ret_mem_unit_eval e.lhs m input start finish label payload).trans
      ((and_congr (finite label payload) Iff.rfl).trans
        (ret_mem_unit_eval e.rhs m input start finish label payload).symm)

theorem empty_state_satisfies [IsEmpty σ] (e : Equation P) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts e.inputs)) :
    (fiberRoom.{u, v, w, x} P e.inputs.length).Sat (Discrete.mk (inputModel m σ input))
      (translateEquation e) := by
  change ssaBeh 1 (inputModel m σ input) (scope e.lhs) =
    ssaBeh 1 (inputModel m σ input) (scope e.rhs)
  apply Set.ext
  intro observation
  cases observation with
  | ret start _ _ | fault start _ | diverge start => exact isEmptyElim (show σ from start)

end Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber.Proofs
