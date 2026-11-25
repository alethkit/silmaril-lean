module

public import Silmaril.SSA.MLIR.Institution.Arith.Defs
public import Silmaril.SSA.MLIR.Arith.LetIter.Thms
import Silmaril.Proofs.SSA.MLIR.Institution.Arith

public section

namespace Silmaril.MLIR.Institution.Arith

open Silmaril.MLIR.Arith (Width Env Atom instr word)
open Silmaril.Isotope
open Silmaril.Isotope.Morphism
open Silmaril.Isotope.LambdaSSA

variable {Γ : List Width} {w : Width}

/-- Translating an open arithmetic SSA block into the institution preserves its denotation. -/
theorem translate_denote (block : Silmaril.MLIR.Arith.Block Γ w) (env : Env Γ) :
    (translate block).denote model (assignment env) = block.denote env :=
  Proofs.MLIR.Institution.Arith.translate_denote block env

/-- The existing single-exit LambdaSSA lowering computes the institution denotation. -/
theorem translate_lambdaSSA_eval_iff (block : Silmaril.MLIR.Arith.Block Γ w) (env : Env Γ)
    (label : Nat) (out : Value Atom) :
    Semantics.Region.Eval instr env.toLambdaSSA block.toLambdaSSA () label out () ↔
      label = 0 ∧ out = word (w := w) ((translate block).denote model (assignment env)) := by
  rw [translate_denote]
  exact block.toLambdaSSA_eval_iff env label out

/-- The single-exit LetIter encoding computes the same result on typed inputs. -/
theorem translate_letIter_eval_iff (block : Silmaril.MLIR.Arith.Block Γ w) (env : Env Γ)
    (out : Value Atom) :
    LetIter.Semantics.Eval instr Empty.elim env.toLetIter block.toLetIter () out () ↔
      out = word (w := w) ((translate block).denote model (assignment env)) := by
  rw [translate_denote]
  exact block.toLetIter_eval_iff env out

end Silmaril.MLIR.Institution.Arith
