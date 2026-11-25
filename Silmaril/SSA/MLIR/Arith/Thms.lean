module

public import Silmaril.SSA.MLIR.Arith.Defs
import Silmaril.Proofs.SSA.MLIR.Arith.Correctness

/-! The lowering preserves types and has exactly the source block's denotation. -/

public section

namespace Silmaril.MLIR.Arith

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

variable {Γ : List Width} {w : Width}

/-- The lowered block has a single exit with the declared result type. -/
theorem Block.toLambdaSSA_hasType (block : Block Γ w) :
    Region.HasType (Γ.map Ty.base) block.toLambdaSSA [.base w] :=
  Proofs.MLIR.Arith.toLambdaSSA_hasType block

/-- For every typed input, the lowered block exits exactly at label zero with
the source result. This covers both straight-line blocks and scoped bodies. -/
theorem Block.toLambdaSSA_eval_iff (block : Block Γ w) (env : Env Γ)
    (label : Nat) (out : Value Atom) :
    Semantics.Region.Eval instr env.toLambdaSSA block.toLambdaSSA () label out () ↔
      label = 0 ∧ out = word (block.denote env) :=
  Proofs.MLIR.Arith.toLambdaSSA_eval_iff block env label out

end Silmaril.MLIR.Arith
