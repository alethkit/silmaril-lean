module

public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Iteration.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Packing.Iteration

/-! # Exact iteration on a packed state -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory LocallyNameless

variable {S : Sig.{u}}

/-- Pure uniformity reexpresses a packed loop as iteration on the whole packed state. -/
theorem packedArrow_iter_state {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b (coprod B A)) :
    packedArrow (S := S) (.iter ha hb) =
      pairArrows (𝟙 (of (packType β))) (packedArrow ha) ≫
        iterate (packedArrow (carriedIterTyping hb)) :=
  packedArrow_iter_state_proof ha hb

/-- Repacking the recursive state discards the previous state and preserves the outer context. -/
theorem packedArrow_carriedState {n : Nat} (β : BoundCtx S.Ty n) (X A : S.Ty) :
    let R := of (S := S) (packType β)
    let P := productObj R (of X)
    packedArrow (S := S) ((packTermTyping (β.snoc A)).underBinder (X := X)) =
      pairArrows (first P (of A) ≫ first R (of X)) (second P (of A)) :=
  packedArrow_carriedState_proof β X A

end Silmaril.Thesis.LambdaIter.Syn.SynCat
