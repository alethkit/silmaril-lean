module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Correctness
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms

/-! # Exact dominance and certificate-free invocation for the lowered loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance

open Silmaril.MLIR.Arith (Env Width)
open Loop.MLIR.CF (Program evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable (g : Program Input carried result entrySigs headerSigs)

/-- The typed lowering emits exactly these successor occurrences. -/
theorem lower_targets (block : BlockId (SourceLabel carried result)) :
    (shape (lower g) block).target = expectedTarget block :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.lower_targets g block

/-- Address ancestry is exact for structural paths on the emitted CFG. -/
theorem prefix_iff_dominates (a b : BlockId (SourceLabel carried result)) :
    List.IsPrefix (address a) (address b) ↔ Dominates (lower g) a b :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.prefix_iff_dominates g a b

theorem address_injective {a b : BlockId (SourceLabel carried result)}
    (same : address a = address b) : a = b :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.address_injective same

/-- Every vertex in the three-block inventory has a structural entry path. -/
theorem lower_reachable (block : BlockId (SourceLabel carried result)) : Reachable (lower g) block :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.reachable g block

/-- Construct the executable address table and reachable mask for this lowering. -/
def certificate : DominatorTree (lower g) where
  address := address
  entry_address := rfl
  address_injective := address_injective
  reachable := fun _ => true
  reachable_sound := fun {block} _ => lower_reachable g block
  prefix_sound := fun {a b} _ ancestry => (prefix_iff_dominates g a b).mp ancestry

theorem certificate_complete : (certificate g).Complete where
  reachable_complete := fun _ => rfl
  prefix_complete := fun {a b} _ dominates => (prefix_iff_dominates g a b).mpr dominates

/-- Call the existing first-binding hoist with the constructed certificate. -/
def pickAndHoist? : Option (Point (SourceLabel carried result) × Output Input carried result) :=
  LoopHoist.pickAndHoist? g (certificate g)

variable {g} {cut : Point (SourceLabel carried result)} {output : Output Input carried result}

theorem pickAndHoist?_run_eq (picked : pickAndHoist? g = some (cut, output))
    (input : Env Input) (fuel : Nat) :
    output.2.run evalOp fuel input = (lower g).run evalOp fuel input :=
  LoopHoist.pickAndHoist?_run_eq (tree := certificate g) picked input fuel

theorem pickAndHoist?_budget (picked : pickAndHoist? g = some (cut, output))
    (input : Env Input) (budget : Nat) :
    output.2.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  LoopHoist.pickAndHoist?_budget (tree := certificate g) picked input budget

theorem pickAndHoist?_returns_iff (picked : pickAndHoist? g = some (cut, output))
    (input : Env Input) (value : BitVec result.val) :
    g.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input) value ↔
      ∃ fuel, output.2.run evalOp fuel input = some (.cons value .nil) :=
  LoopHoist.pickAndHoist?_returns_iff (tree := certificate g) picked input value

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance
