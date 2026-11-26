module

public import Silmaril.SSA.SeaOfNodes.Quads.Join.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Correctness

/-! # Exact edge and return agreement for one closed quad join -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Join

open RVSDG (Locals Tuple Wires)
open Diamond (Ty ValueSort Signature Model Val dataPorts Merge Projection)

universe u v w
variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

/-- Slot order associates each selected edge with its own If projection. -/
theorem predecessor_selected (merge : Merge) (condition : Bool) :
    merge.predecessor (selected merge condition) = Projection.ofBool condition :=
  Proofs.predecessor_selected merge condition

/-- The lowered block's result wires come from its final version map. -/
theorem Block.lowerFrom_results {args outs : List (Ty Data)} {past : List (List (Ty Data))}
    (block : Block Op regs) (exit : Exit regs outs) (current : Wires args past (dataPorts regs)) :
    (block.lowerFrom current exit).toGraph.results = exit.select (block.versions current) :=
  Proofs.lowerFrom_results block exit current

/-- A block computes the source bank from any typed reaching-version map. -/
theorem Block.lowerFrom_eval {args outs : List (Ty Data)} {past : List (List (Ty Data))}
    (block : Block Op regs) (exit : Exit regs outs)
    (m : Model.{u, v, w} Op) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) (current : Wires args past (dataPorts regs)) :
    (block.lowerFrom current exit).eval (model m) entry locals =
      exit.select (block.eval m (current.read entry locals)) :=
  Proofs.lowerFrom_eval block exit m entry locals current

/-- The numbered child graph returns the independently computed incoming column. -/
theorem Program.arm_results (p : Program Op regs out) (i : Fin 2) :
    (p.arm i).toGraph.results = p.incoming (slotAt i) :=
  Proofs.arm_results p i

/-- Evaluating an incoming column delivers exactly that predecessor's final bank. -/
theorem Program.arm_run (p : Program Op regs out) (i : Fin 2) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    (p.arm i).toGraph.run (model m) entry = (p.predecessor (slotAt i)).eval m entry :=
  Proofs.arm_graph_run p i m entry

/-- The numbered graph selects the corresponding predecessor and runs the join
with its typed arguments, returning the same value as ordered execution. -/
theorem Program.lower_run (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    p.lower.run (model m) entry = .cons (p.eval m entry) .nil :=
  Proofs.lower_run p m entry

end Silmaril.SSA.SeaOfNodes.Quads.Join
