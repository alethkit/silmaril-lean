module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Thms
public import Silmaril.Semantics.ITree.Trace.Thms

/-! # Pointwise finite trace order for two checked φ graphs -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture

open Silmaril.SSA.LambdaRTL
open Silmaril.Elgot.ITree (TraceLE)
open LambdaSSA.Semantics.Interaction (Primitive)

universe u v w x
variable {Events : Type u → Type u} {F : Type v} {G : Type w}
  {V W K J Base α : Type (u + 1)} {n : Nat}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  [HasTy F (Ty Base)] [HasTy G (Ty Base)]
variable {left : CFG.Cyclic.Phi.Graph V K F} {right : CFG.Cyclic.Phi.Graph W J G}
  {leftInputs : List V} {rightInputs : List W}
  {leftNames : Fin n → Option V} {rightNames : Fin n → Option W}
  {leftProfile rightProfile : BoundCtx (Ty Base) n}
  {leftBlocks : Fin (blockCount left) → Ty Base} {rightBlocks : Fin (blockCount right) → Ty Base}
  {leftExit rightExit : Fin 1 → Ty Base}
  {leftAdmission : Admission left leftInputs leftNames leftProfile leftBlocks leftExit}
  {rightAdmission : Admission right rightInputs rightNames rightProfile rightBlocks rightExit}

/-- The canonical pure packed evaluator has the same observation as its
independent source evaluator at the given store. -/
theorem packedObservation_eq_sourceObservation (closed : Closed leftAdmission)
    (instr : Primitive Events F α) (store : V → Value α) :
    packedObservation closed instr store = sourceObservation instr left store :=
  packed_run_tree closed instr store

/-- Finite trace inclusion at one matched input is equivalent on the two
independent source runs and on their actual checked packed dispatchers.
Source returns use the same outward encoding on both sides. -/
theorem packed_traceLE_iff (closedLeft : Closed leftAdmission) (closedRight : Closed rightAdmission)
    (leftPrim : Primitive Events F α) (rightPrim : Primitive Events G α)
    (input : MatchedInputs leftProfile rightProfile leftExit rightExit leftNames rightNames) :
    TraceLE.{u, u+1} (packedObservation closedLeft leftPrim input.leftStore)
        (packedObservation closedRight rightPrim input.rightStore) ↔
      TraceLE.{u, u+1} (sourceObservation leftPrim left input.leftStore)
        (sourceObservation rightPrim right input.rightStore) := by
  rw [packedObservation_eq_sourceObservation, packedObservation_eq_sourceObservation]

/-- Transport pointwise inclusion over any family of matched inputs.
A common event type fixes the meaning of requests and typed replies. -/
theorem packed_pointwise_traceLE_iff {I : Type x}
    (closedLeft : Closed leftAdmission) (closedRight : Closed rightAdmission)
    (leftPrim : Primitive Events F α) (rightPrim : Primitive Events G α)
    (stores : I → MatchedInputs leftProfile rightProfile leftExit rightExit leftNames rightNames) :
    (∀ i, TraceLE.{u, u+1} (packedObservation closedLeft leftPrim (stores i).leftStore)
        (packedObservation closedRight rightPrim (stores i).rightStore)) ↔
      (∀ i, TraceLE.{u, u+1} (sourceObservation leftPrim left (stores i).leftStore)
        (sourceObservation rightPrim right (stores i).rightStore)) :=
  forall_congr' fun i => packed_traceLE_iff closedLeft closedRight leftPrim rightPrim (stores i)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
