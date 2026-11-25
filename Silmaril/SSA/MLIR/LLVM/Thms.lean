module

public import Silmaril.SSA.MLIR.LLVM.Defs
public import Silmaril.SSA.MLIR.Arith.LetIter.Thms
import Silmaril.Proofs.SSA.MLIR.LLVM.Correctness

public section

namespace Silmaril.MLIR.LLVM

open Arith (Atom Env Width word)
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA

variable {Γ : List Width} {w : Width}

/-- Unsigned division on defined bits raises immediate UB exactly on a zero divisor. -/
theorem BinOp.eval_udiv_eq_error_iff {bits : Nat} (lhs rhs : BitVec bits) :
    BinOp.udiv.eval lhs rhs = .error .divisionByZero ↔ rhs = 0 := by
  by_cases zero : rhs = 0 <;> simp [BinOp.eval, zero]

/-- A nonzero divisor yields the quotient of the unsigned operand values. -/
theorem BinOp.eval_udiv_of_ne_zero {bits : Nat} (lhs rhs : BitVec bits) (nonzero : rhs ≠ 0) :
    BinOp.udiv.eval lhs rhs = .ok (BitVec.ofNat bits (lhs.toNat / rhs.toNat)) := by
  rw [BinOp.eval, ite_eq_right nonzero, BitVec.udiv_def]

/-- A successful translation evaluates to the same bits on every concrete environment. -/
theorem Block.eval_eq_of_toArith (block : Block Γ w) (arith : Arith.Block Γ w)
    (lowered : block.toArith = some arith) (env : Env Γ) :
    block.eval env = .ok (arith.denote env) :=
  Proofs.MLIR.LLVM.eval_eq_of_toArith block arith lowered env

/-- Every finite target observation is a source result at exit zero, and every
source result is observed by the target at that exit. -/
theorem Block.toLambdaSSA_eval_iff (block : Block Γ w) (arith : Arith.Block Γ w)
    (lowered : block.toArith = some arith) (env : Env Γ) (label : Nat) (out : Value Atom) :
    Semantics.Region.Eval Arith.instr env.toLambdaSSA arith.toLambdaSSA () label out () ↔
      label = 0 ∧ ∃ result, block.eval env = .ok result ∧ out = word result :=
  Proofs.MLIR.LLVM.toLambdaSSA_eval_iff block arith lowered env label out

/-- Finite LetIter observations are exactly the concrete source result. -/
theorem Block.toLetIter_eval_iff (block : Block Γ w) (arith : Arith.Block Γ w)
    (lowered : block.toArith = some arith) (env : Env Γ) (out : Value Atom) :
    LetIter.Semantics.Eval Arith.instr Empty.elim env.toLetIter arith.toLetIter () out () ↔
      ∃ result, block.eval env = .ok result ∧ out = word result :=
  Proofs.MLIR.LLVM.toLetIter_eval_iff block arith lowered env out

end Silmaril.MLIR.LLVM
