module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Forward

/-! # Forward edges of compiled acyclic bodies -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A : τ} {L : List τ}

/-- Every emitted block edge goes to a greater label number. This includes
edges to the surrounding continuation labels. -/
theorem Compiled.blockAt_forward (p : Compiled Φ L A) (i : Fin (p.rest.locals.length + 1))
    (target : Nat) (mem : target ∈ (p.blockAt i).targets) : i.val < target :=
  Proofs.blockAt_forward p i target mem

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic
