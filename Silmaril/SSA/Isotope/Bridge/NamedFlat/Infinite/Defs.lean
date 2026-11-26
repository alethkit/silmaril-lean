module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Semantics.Defs

/-! # Infinite internal transfers of a named lexical CFG -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL

universe u
variable {V K F α : Type u} [DecidableEq V] [DecidableEq K]

/-- The entry succeeds, and every transfer in the sequence executes an
internal block successfully. Each step uses the same table and input store
as the named lexical runner. -/
def InfiniteRun (prim : F → Value α → Part (Value α)) (graph : CFG V K F)
    (store : V → Value α) : Prop :=
  ∃ path : Nat → K × Value α,
    path 0 ∈ graph.entry.evalJump (model prim) store ∧
    ∀ i, Sum.inr (path (i + 1)) ∈ CFG.Cyclic.stepSSA (model prim) graph.blocks store (path i)

end Silmaril.Isotope.Bridge.NamedFlat
