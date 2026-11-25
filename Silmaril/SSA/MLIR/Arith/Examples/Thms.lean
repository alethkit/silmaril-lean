module

public import Silmaril.SSA.MLIR.Arith.Examples.Defs
public import Silmaril.SSA.MLIR.Arith.LetIter.Thms

public section

namespace Silmaril.MLIR.Arith.Examples

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA

/-- The operation-to-block rewrite preserves modular arithmetic at every width. -/
theorem double_lowering (w : Width) (env : Env [w]) :
    (doubleAdd w).denote env = (doubleMul w).denote env :=
  BitVec.mul_two.symm

/-- The rewritten LambdaSSA block sends twice 200 modulo 256 to exit zero. -/
theorem doubleMul_lambdaSSA :
    Semantics.Region.Eval instr (Env.cons (w := i8) 200#8 .nil).toLambdaSSA
      (doubleMul i8).toLambdaSSA () 0 (word (w := i8) 144#8) () :=
  ((doubleMul i8).toLambdaSSA_eval_iff _ _ _).mpr ⟨rfl, rfl⟩

/-- The scoped region yields 20 squared, then the enclosing block adds 20.
The translated LetIter term returns 420 modulo 256. -/
theorem squareAdd_letIter :
    LetIter.Semantics.Eval instr Empty.elim
      (Env.cons (w := i1) 1#1 (.cons (w := i8) 20#8 .nil)).toLetIter
      squareAdd.toLetIter () (word (w := i8) 164#8) () :=
  (squareAdd.toLetIter_eval_iff _ _).mpr rfl

end Silmaril.MLIR.Arith.Examples
