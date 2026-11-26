module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Simulation

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Pending assign execute)
open Silmaril.Elgot (mapReturn)
open Silmaril.Elgot.ITree (TraceLE resume)
open LambdaSSA.Semantics.Interaction (Primitive)

universe u v w
variable {Events : Type u → Type u} {V W K J Base α : Type (u + 1)} {F : Type v} {G : Type w}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  {left : Graph V K F} {right : Graph W J G}
  {leftPrim : Primitive Events F α} {rightPrim : Primitive Events G α}

/-- On a resolved jump the local tree runs the target with its parallel φ
assignments, using the outgoing store as the snapshot for every operand. -/
theorem step_jump (instr : Primitive Events F α) (graph : Graph V K F)
    (pred : Option K) (target : K) (store : V → Value α)
    {block : CFG.Cyclic.Phi.Block V K F} (found : graph.blocks.lookup target = some block) :
    stepTree instr graph (.jump pred target, store) =
      (Sum.inr : Pending V K (Value α) → BodyResult V K α) <$>
        execute (treeModel instr) (some target) block.body
          (assign (treeModel instr) pred store block.rows store) := by
  simp [stepTree, mapReturn, CFG.Cyclic.Phi.step, found, ← bind_pure_comp, bind_assoc]

/-- A return boundary exposes the explicitly tagged single exit. -/
theorem step_return (instr : Primitive Events F α) (graph : Graph V K F)
    (value : Value α) (store : V → Value α) :
    stepTree instr graph (.returned value, store) = pure (.inl (0, .inl value)) := by
  simp [stepTree, mapReturn, CFG.Cyclic.Phi.step]
  rfl

theorem sourceObservation_eq_resume (instr : Primitive Events F α) (graph : Graph V K F)
    (store : V → Value α) :
    sourceObservation instr graph store = resume (stepTree instr graph) (entryTree instr graph store) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.LocalTrace.sourceObservation_eq_resume instr graph store

/-- Local simulation of the entry and paired block boundaries gives source
trace inclusion. Each nonempty observation supplies a finite left prefix up
to its next request or exit. Each matching right prefix is finite by
`Silent`, so no separate global termination premise is needed. -/
theorem Simulation.source_le (sim : Simulation leftPrim rightPrim left right)
    {leftStore : V → Value α} {rightStore : W → Value α}
    (entry : sim.residual (entryTree leftPrim left leftStore) (entryTree rightPrim right rightStore)) :
    TraceLE (sourceObservation leftPrim left leftStore)
      (sourceObservation rightPrim right rightStore) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.LocalTrace.source_le sim entry

variable {n : Nat} [HasTy F (Ty Base)] [HasTy G (Ty Base)]
  {leftInputs : List V} {rightInputs : List W}
  {leftNames : Fin n → Option V} {rightNames : Fin n → Option W}
  {leftProfile rightProfile : BoundCtx (Ty Base) n}
  {leftBlocks : Fin (blockCount left) → Ty Base} {rightBlocks : Fin (blockCount right) → Ty Base}
  {leftExit rightExit : Fin 1 → Ty Base}
  {leftAdmission : Admission left leftInputs leftNames leftProfile leftBlocks leftExit}
  {rightAdmission : Admission right rightInputs rightNames rightProfile rightBlocks rightExit}

/-- The same local witness suffices for the two actual checked packed runs
at any aligned input whose entries satisfy the residual relation. -/
theorem Simulation.packed_le (sim : Simulation leftPrim rightPrim left right)
    (closedLeft : Closed leftAdmission) (closedRight : Closed rightAdmission)
    (input : MatchedInputs leftProfile rightProfile leftExit rightExit leftNames rightNames)
    (entry : sim.residual (entryTree leftPrim left input.leftStore)
      (entryTree rightPrim right input.rightStore)) :
    TraceLE (packedObservation closedLeft leftPrim input.leftStore)
      (packedObservation closedRight rightPrim input.rightStore) :=
  (packed_traceLE_iff closedLeft closedRight leftPrim rightPrim input).2 (sim.source_le entry)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local
