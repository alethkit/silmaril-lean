module

public import Silmaril.SSA.MLIR.LLVM.Defs
public import Silmaril.SSA.MLIR.Arith.LetIter.Thms

/-! Evaluation of the shared scalar operations and their calculus translations. -/

public section

namespace Silmaril.Proofs.MLIR.LLVM

open Silmaril.MLIR
open Silmaril.MLIR.LLVM
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA

variable {Γ : List Arith.Width} {w : Arith.Width}

private theorem rhs_eval (rhs : Rhs Γ w) (arith : Arith.Rhs Γ w)
    (lowered : rhs.toArith = some arith) (env : Arith.Env Γ) :
    rhs.eval env = .ok (arith.denote env) := by
  cases rhs with
  | constant value => cases lowered; rfl
  | binary op lhs rhs => cases op <;> cases lowered <;> rfl

theorem eval_eq_of_toArith (block : Block Γ w) (arith : Arith.Block Γ w)
    (lowered : block.toArith = some arith) (env : Arith.Env Γ) :
    block.eval env = .ok (arith.denote env) := by
  induction block with
  | ret value => cases lowered; rfl
  | letOp rhs rest ih =>
      cases hRhs : rhs.toArith with
      | none => simp [Block.toArith, hRhs] at lowered
      | some arithRhs =>
          cases hRest : rest.toArith with
          | none => simp [Block.toArith, hRhs, hRest] at lowered
          | some arithRest =>
              have eq : Arith.Block.letOp arithRhs arithRest = arith := by
                simpa [Block.toArith, hRhs, hRest] using lowered
              subst arith
              change (rhs.eval env >>= fun value => rest.eval (.cons value env)) = _
              rw [rhs_eval rhs arithRhs hRhs env]
              exact ih arithRest hRest (.cons (arithRhs.denote env) env)

theorem toLambdaSSA_eval_iff (block : Block Γ w) (arith : Arith.Block Γ w)
    (lowered : block.toArith = some arith) (env : Arith.Env Γ) (label : Nat)
    (out : Value Arith.Atom) :
    Semantics.Region.Eval Arith.instr env.toLambdaSSA arith.toLambdaSSA () label out () ↔
      label = 0 ∧ ∃ result, block.eval env = .ok result ∧ out = Arith.word result := by
  rw [arith.toLambdaSSA_eval_iff, eval_eq_of_toArith block arith lowered env]
  simp

theorem toLetIter_eval_iff (block : Block Γ w) (arith : Arith.Block Γ w)
    (lowered : block.toArith = some arith) (env : Arith.Env Γ) (out : Value Arith.Atom) :
    LetIter.Semantics.Eval Arith.instr Empty.elim env.toLetIter arith.toLetIter () out () ↔
      ∃ result, block.eval env = .ok result ∧ out = Arith.word result := by
  rw [arith.toLetIter_eval_iff, eval_eq_of_toArith block arith lowered env]
  simp

end Silmaril.Proofs.MLIR.LLVM
