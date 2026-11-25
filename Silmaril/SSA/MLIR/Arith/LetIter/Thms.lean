module

public import Silmaril.SSA.MLIR.Arith.LetIter.Defs

public section

namespace Silmaril.MLIR.Arith

open Silmaril.Isotope
open Silmaril.Isotope.Morphism

variable {Γ : List Width} {w : Width}

private theorem letIterContext_toList (Γ : List Width) :
    (letIterContext Γ).toList = Γ.map Ty.base := by
  induction Γ <;> simp_all [letIterContext, BoundCtx.toList]

/-- The translated LetIter term has the same input and result types. -/
theorem Block.toLetIter_hasType (block : Block Γ w) :
    LetIter.LocallyNameless.HasType Prim .nil (letIterContext Γ) block.toLetIter (.base w) :=
  SSAIter.encodeSingle_hasType _ (letIterContext_toList Γ ▸ block.toLambdaSSA_hasType)

/-- The translated LetIter term returns exactly the source result, on the same inputs. -/
theorem Block.toLetIter_eval_iff (block : Block Γ w) (env : Env Γ) (out : Value Atom) :
    LetIter.Semantics.Eval instr Empty.elim env.toLetIter
      block.toLetIter () out () ↔ out = word (block.denote env) := by
  refine (SSAIter.encodeSingle_eval_iff _ (env := env.toLambdaSSA) (fun _ => rfl)).trans ?_
  simpa [Block.toScopedLambdaSSA] using block.toLambdaSSA_eval_iff env 0 out

end Silmaril.MLIR.Arith
