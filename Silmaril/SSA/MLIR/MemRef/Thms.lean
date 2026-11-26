module

public import Silmaril.SSA.MLIR.MemRef.Defs

/-! Evaluation equations for the typed initialized MemRef fragment. -/

public section

namespace Silmaril.MLIR.MemRef

open SSA.RVSDG (Locals Tuple)
open SSA.RVSDG.OrderedRuntime.Structured (Values)
open SSA.RVSDG.MLIR.Graph.Feedback (Code Operands)

variable {cells : Nat} {scope : List (List (Ty cells))}
variable {ins results outs : List (Ty cells)}

theorem run_yield (wires : Operands scope outs)
    (env : Locals (Values (Value cells)) scope) (initial : Buffer cells) :
    run ⟨.yield wires, trivial⟩ env initial = (wires.read .nil env, initial) := by
  simp only [run, Code.runStraightLine]
  rfl

theorem run_prim (op : Op cells ins results) (wires : Operands scope ins)
    (rest : Block cells (scope ++ [results]) outs)
    (env : Locals (Values (Value cells)) scope) (initial : Buffer cells) :
    run ⟨.prim op wires rest.val, rest.property⟩ env initial =
      let (result, next) := (model cells).effect op (wires.read .nil env) initial
      run rest (env.snoc result) next := by
  simp only [run, Code.runStraightLine]
  rfl

theorem load_effect (ref : Reference cells) (index : Fin cells) (buffer : Buffer cells) :
    (model cells).effect .load (.cons ref (.cons index .nil)) buffer =
      (.cons (buffer.cell index) .nil, buffer) :=
  rfl

theorem store_effect (word : Word) (ref : Reference cells) (index : Fin cells) (buffer : Buffer cells) :
    (model cells).effect .store (.cons word (.cons ref (.cons index .nil))) buffer =
      (.nil, ⟨Function.update buffer.cell index word⟩) :=
  rfl

end Silmaril.MLIR.MemRef
