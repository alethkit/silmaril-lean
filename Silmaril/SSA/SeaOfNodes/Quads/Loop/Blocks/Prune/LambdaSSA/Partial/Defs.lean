module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Defs

/-! The partial observation of the actual λSSA evaluation relation. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial

open Diamond (Model ValueSort)
open Diamond.LambdaSSA (Atom Primitive inputEnv instruction)
open Isotope (Value)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Region (Eval)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}

abbrev Observation (m : Model.{u, v, w} Op) (σ : Type x) := Nat × Value (Atom m) × σ

/-- Observe a finite region evaluation with the quad primitive interpretation
at the typed bank and ambient state. The outcome retains all exit data. -/
noncomputable def observe {regs : List (ValueSort Data)} {σ : Type x}
    (m : Model.{u, v, w} Op) (input : Bank (regs := regs) m)
    (code : Region (Primitive Op)) (start : σ) : Part (Observation m σ) where
  Dom := ∃ result : Observation m σ,
    Eval (instruction m) (inputEnv m input) code start result.1 result.2.1 result.2.2
  get := Classical.choose

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial
