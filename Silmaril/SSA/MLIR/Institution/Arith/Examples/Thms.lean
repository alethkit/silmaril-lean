module

public import Silmaril.SSA.MLIR.Institution.Arith.Examples.Defs
public import Silmaril.SSA.MLIR.Institution.Arith.Thms
public import Silmaril.SSA.MLIR.Institution.Thms
public import Silmaril.SSA.MLIR.Arith.Examples.Thms

public section

namespace Silmaril.MLIR.Institution.Arith.Examples

open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.Arith.Examples (squareAdd doubleAdd doubleMul double_lowering)

/-- Interpreting the tagged scoped example still yields `20 * 20 + 20` modulo 256. -/
theorem squareAdd_tag_denote :
    ((translate squareAdd).map tag).denote taggedModel (assignment squareInput) = 164#8 :=
  (Term.denote_map tag taggedModel (translate squareAdd) (assignment squareInput)).trans
    ((translate_denote squareAdd squareInput).trans rfl)

/-- The existing operation-to-block rewrite agrees in the interpreted fragment at every width. -/
theorem double_lowering_denote (w : Width) (env : Env [w]) :
    (translate (doubleAdd w)).denote model (assignment env) =
      (translate (doubleMul w)).denote model (assignment env) := by
  rw [translate_denote, translate_denote]
  exact double_lowering w env

end Silmaril.MLIR.Institution.Arith.Examples
