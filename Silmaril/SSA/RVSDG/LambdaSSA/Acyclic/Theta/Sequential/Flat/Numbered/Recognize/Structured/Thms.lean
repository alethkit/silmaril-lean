module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured

/-! # Completeness for generated sequence and binary γ bodies -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ] [DecidableEq Φ]
variable {A I B K M C J E D : τ}

/-- The exact recognizer reconstructs generated right-associated components,
including the typed instruction sequence and recursively nested γ arms. -/
theorem recognize_rightAssociated (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (hp : RightAssociated p.loop.body) (hq : RightAssociated q.body) :
    recognize (compile p q) = some ⟨⟨B, K, C, J, p, q⟩, rfl⟩ :=
  Proofs.recognize_rightAssociated p q hp hq

/-- Every generated linked graph is accepted, with arbitrary association
of sequences and arbitrary nesting of binary choices in either body. -/
theorem complete_generated (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D) :
    (recognize (compile p q)).isSome = true :=
  Proofs.complete_generated p q

/-- Executable acceptance characterizes this generated graph family at
its literal numbering. A successful match itself gives the witness. -/
theorem recognize_isSome_iff (g : Graph Φ A I M E D) :
    (recognize g).isSome = true ↔ ∃ c : Components Φ A I M E D, c.graph = g :=
  Proofs.recognize_isSome_iff g

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize
