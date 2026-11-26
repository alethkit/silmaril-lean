module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Defs

/-! # The exact branch/join equation -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open LambdaSSA.Acyclic (Code Operand)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {n : Nat} {β : BoundCtx τ n} {A B D E : τ}

/-- Compare a shared join after a case with a copy of its continuation in each arm. -/
def sharedJoinEquation (e : Operand P.Instr β (coprod A B))
    (l : Code P.Instr (β.snoc A) D) (r : Code P.Instr (β.snoc B) D)
    (k : Code P.Instr (β.snoc D) E) : SSAEquation P :=
  ⟨⟨n, β, E⟩, .join (.case e l r) k, Code.distributeJoin e l r k⟩

end Silmaril.Isotope.Institution.Acyclic
