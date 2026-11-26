module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {first : AfterReorder.Plan} {consumerOrigin : Nat}
variable {prepared : Prepared Input carried result} {moved : Emission Input carried result}

/-- Replay uses the checked handoff from the exact first emission and then
edits that CFG. -/
theorem replay?_spec (accepted : replay? g first consumerOrigin = some moved) :
    prepare? g first consumerOrigin = some moved.prepared ∧
      emit? moved.prepared = some moved.cfg ∧ AfterReorder.replay? g first = some moved.prepared.intermediate :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_spec accepted

/-- Every accepted handoff supplies the typed structure needed to emit. -/
theorem prepare?_emits (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ target, emit? prepared = some target :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.prepare?_emits accepted

/-- The old leading let is followed by the inserted consumer. The current
header is rewritten at the checked index. Transfers prepend the new
result to the prior header packet and preserve exit arguments exactly. -/
theorem replay?_routes (accepted : replay? g first consumerOrigin = some moved) (input : Env Input) :
    ∃ (args : List Width) (producer : TargetOp args moved.prepared.intermediate.1)
      (operands : Operands Input args) (tail : Block TargetOp (Label moved.prepared.intermediate.1 carried result)
        (moved.prepared.intermediate.1 :: Input) [result]),
      moved.prepared.intermediate.2.entry = .letOp producer operands tail ∧
      moved.cfg.entry = .letOp producer operands
        (.letOp moved.prepared.consumer.op moved.prepared.consumer.inputs (liftCode Var.there .here tail)) ∧
      rewriteAt? moved.prepared.index Var.there .here (moved.prepared.intermediate.2.block .header) =
        some (moved.cfg.block .header) ∧
      moved.cfg.block .exit = .terminator (.ret (.cons .here .nil)) ∧
      let saved := evalOp producer (operands.eval input)
      let value := evalOp moved.prepared.consumer.op (moved.prepared.consumer.inputs.eval (.cons saved input))
      StepRoutes moved.prepared.intermediate.2 moved.cfg input saved value :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_routes accepted input

/-- The second edit preserves both return and exhaustion at the same CFG fuel. -/
theorem replay?_run_eq (accepted : replay? g first consumerOrigin = some moved)
    (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = moved.prepared.intermediate.2.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_run_eq accepted input fuel

/-- Native budget plus the preheader, final header test and exit gives CFG fuel. -/
theorem replay?_budget (accepted : replay? g first consumerOrigin = some moved)
    (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_budget accepted input budget

/-- The complete replay preserves the native lowering's partial denotation. -/
theorem replay?_denotePart (accepted : replay? g first consumerOrigin = some moved) (input : Env Input) :
    (Cfg.embed moved.cfg).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_denotePart accepted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit
