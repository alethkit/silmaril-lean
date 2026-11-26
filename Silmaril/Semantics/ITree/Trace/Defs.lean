module

public import Silmaril.Semantics.ITree.Defs

/-! # Reply-indexed finite observations of weak interaction trees -/

@[expose] public section

namespace Silmaril.Elgot.ITree

universe u v

/-- A finite path records a request with its actual typed reply at each
completed exchange. The endpoint can stop without inspecting the tree,
observe a pending request (even when it has no replies), or observe a return. -/
inductive Trace (E : Type u → Type u) (A : Type v) where
  | prefix
  | request {R : Type u} (event : E R)
  | exchange {R : Type u} (event : E R) (reply : R) (tail : Trace E A)
  | result (value : A)

variable {E : Type u → Type u} {A B : Type v}

/-- Retag only terminating observations. -/
def Trace.map (f : A → B) : Trace E A → Trace E B
  | .prefix => .prefix
  | .request e => .request e
  | .exchange e r tail => .exchange e r (tail.map f)
  | .result a => .result (f a)

/-- Observation follows the continuation of each recorded reply. The
destructor has already hidden silent steps. -/
def HasTrace (t : Tree E A) : Trace E A → Prop
  | .prefix => True
  | .request e => ∃ k, out t = Part.some (.vis e k)
  | .exchange e r tail => ∃ k, out t = Part.some (.vis e k) ∧ HasTrace (k r) tail
  | .result a => out t = Part.some (.ret a)

/-- Inclusion of finite observations, oriented from fewer observations to
more. Silent divergence contributes only the empty prefix. -/
def TraceLE (t s : Tree E A) : Prop :=
  ∀ p, HasTrace t p → HasTrace s p

end Silmaril.Elgot.ITree
