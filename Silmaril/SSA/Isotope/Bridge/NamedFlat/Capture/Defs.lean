module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.Defs

/-! # Capture closure for scoped flat graphs -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Capture

open LambdaSSA
open LetCase.LocallyNameless (Tm)

universe u v w

variable {F : Type v} {labels : Nat}

/-- Recover a scoped flat region at a new context size, keeping its indices.
A CFG binder or an out-of-range variable or label makes reification fail. -/
def reify {n : Nat} : Region F → Option (Flat F labels n)
  | .br i a =>
      if hi : i < labels then (Morphism.CaseSSA.decode? n a).map (.br ⟨i, hi⟩) else none
  | .let₁ a b =>
      (Morphism.CaseSSA.decode? n a).bind fun value => (reify b).map (.let₁ value)
  | .let₂ a b =>
      (Morphism.CaseSSA.decode? n a).bind fun value => (reify b).map (.let₂ value)
  | .case e l r =>
      (Morphism.CaseSSA.decode? n e).bind fun discr =>
        (reify l).bind fun left => (reify r).map (.case discr left)
  | .cfg .. => none

variable {τ : Type u} {blocks exits n : Nat}

/-- A closed entry evaluates the packet producer once, then decodes the original
entry context. Each block keeps exactly its old erased code and label. -/
structure Closes (β : BoundCtx τ n) (input : Tm Empty F 0)
    (openGraph : FiniteCFG F blocks exits n) (closedGraph : FiniteCFG F blocks exits 0) : Prop where
  entry : closedGraph.entry.erase =
    .let₁ (Morphism.CaseSSA.erase input) (openGraph.entry.erase.packInputsDestructure β.toList)
  block : ∀ i, (closedGraph.block i).erase = (openGraph.block i).erase

/-- Runtime values of the exact context, in the order of the typed packet.
The context head is the right field and the empty context is unit. -/
def packEnv {α : Type w} : Nat → Semantics.Env α → Value α
  | 0, _ => .unit
  | n + 1, env => .pair (packEnv n (env ∘ Nat.succ)) (env 0)

end Silmaril.Isotope.Bridge.NamedFlat.Capture
