module

public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Defs

/-! # Carrying the packed bound context in the recursive state -/

@[expose] public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open LocallyNameless LocallyNameless.Tm

variable {S : Sig.{u}}

/-- Keep the external context with the recursive state and leave exits unchanged. -/
def carriedIterTyping {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {b : Tm Empty S.Instr (n + 1)} (hb : HasType S.Instr Ctx.nil (β.snoc A) b (coprod B A)) :
    HasType S.Instr Ctx.nil (β.snoc A)
      (.case b (.inl (.bv 0)) (.inr (underBinder (packTerm (β.snoc A)))))
      (coprod B (packType (β.snoc A))) :=
  .case hb (.inl .newest) (.inr (packTermTyping (β.snoc A)).underBinder)

end Silmaril.Thesis.LambdaIter.Syn.SynCat
