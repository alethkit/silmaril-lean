module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Defs
public import Silmaril.SSA.Isotope.LetCase.Categorical.Defs

/-! # Moving a shared join past a case in structured acyclic λSSA -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Code

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Give each arm its own instance of the join. Reifying the weakened
continuation makes the passed result slot newest and skips the arm payload. -/
def distributeJoin {n : Nat} {β : BoundCtx τ n} {A B D E : τ}
    (e : Operand Φ β (coprod A B)) (l : Code Φ (β.snoc A) D) (r : Code Φ (β.snoc B) D)
    (k : Code Φ (β.snoc D) E) : Code Φ β E :=
  .case e (.join l (ofLetCase (k.toLetCase.2.underBinder (X := A))))
    (.join r (ofLetCase (k.toLetCase.2.underBinder (X := B))))

end Silmaril.Isotope.LambdaSSA.Acyclic.Code
