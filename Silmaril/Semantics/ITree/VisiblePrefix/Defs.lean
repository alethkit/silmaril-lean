module

public import Silmaril.Semantics.ITree.Defs

/-! # Finite visible prefixes of weak interaction trees -/

@[expose] public section

namespace Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A : Type v}

/-- Some sequence of replies allows at least this many visible events.
The empty prefix exists even when the tree has no visible observation. -/
def HasVisiblePrefix : Nat → Tree E A → Prop
  | 0, _ => True
  | n + 1, t => ∃ (R : Type u) (e : E R) (k : R → Tree E A) (r : R),
      out t = Part.some (.vis e k) ∧ HasVisiblePrefix n (k r)

/-- Every path has at most the supplied number of visible events. -/
def VisibleDepthLE (t : Tree E A) (d : Nat) : Prop :=
  ∀ n, HasVisiblePrefix n t → n ≤ d

end Silmaril.Elgot.ITree
