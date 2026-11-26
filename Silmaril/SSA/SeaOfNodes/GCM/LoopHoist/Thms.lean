module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Correctness

/-! # Certified preheader placement, routing and loop observations -/

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Frame Terminator)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {tree : DominatorTree (lower g)}
variable {cut : Point (SourceLabel carried result)} {output : Output Input carried result}

/-- Successful motion uses the enumerated preheader cut chosen by the
checked natural-loop ranking for the actual first header binding. -/
theorem pickAndHoist?_placement (picked : pickAndHoist? g tree = some (cut, output)) :
    cut = ⟨none, 0⟩ ∧ cut ∈ candidateCuts (lower g) blocks ∧
    ∃ (args : List Width) (op : TargetOp args output.1)
      (operands : Operands (carried :: Input) args)
      (rest : Block TargetOp (SourceLabel carried result) (output.1 :: carried :: Input) [result]),
      (lower g).block .header = .letOp op operands rest ∧
      LoopForest.choosePlacement tree blocks (operandSites operands) (useSites 0 1 rest) = some cut ∧
      Legal (lower g) (operandSites operands) (useSites 0 1 rest) cut :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickAndHoist?_placement picked

/-- The entry supplies one saved value. Every header transfer repeats that
value, alongside the original latch word. Exit transfers keep their original
payload. -/
theorem pickAndHoist?_routes (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) :
    ∃ (args : List Width) (op : TargetOp args output.1)
      (operands : Operands (carried :: Input) args) (captured : Operands Input args)
      (rest : Block TargetOp (SourceLabel carried result) (output.1 :: carried :: Input) [result]),
      (lower g).block .header = .letOp op operands rest ∧ capture? operands = some captured ∧
      let value := evalOp op (captured.eval input)
      output.2.entry.eval evalOp (fun term env => Terminator.eval env term) input =
        ((lower g).entry.eval evalOp (fun term env => Terminator.eval env term) input).map
          (carryFrame value) id ∧
      ∀ frame : Frame (SourceLabel carried result),
        let routed := carryFrame value frame
        (output.2.block routed.label).eval evalOp (fun term env => Terminator.eval env term)
          (routed.args.append input) =
          (((lower g).block frame.label).eval evalOp (fun term env => Terminator.eval env term)
            (frame.args.append input)).map (carryFrame value) id :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickAndHoist?_routes picked input

/-- The emitted CFG has the same observation at every CF fuel budget. -/
theorem pickAndHoist?_run_eq (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) (fuel : Nat) :
    output.2.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickAndHoist?_run_eq picked input fuel

/-- One unit of backedge budget still corresponds to one header traversal.
The preheader, final header test and exit account for three extra blocks. -/
theorem pickAndHoist?_budget (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) (budget : Nat) :
    output.2.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickAndHoist?_budget picked input budget

/-- The emitted CFG preserves and reflects all finite source-loop returns. -/
theorem pickAndHoist?_returns_iff (picked : pickAndHoist? g tree = some (cut, output))
    (input : Env Input) (value : BitVec result.val) :
    g.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input) value ↔
      ∃ fuel, output.2.run evalOp fuel input = some (.cons value .nil) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.pickAndHoist?_returns_iff picked input value

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
