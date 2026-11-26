module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Thms

/-! # Typechecking, exact fuel and finite returns of the pruned CFG -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA

open Diamond (Model ValueSort)
open Diamond.LambdaSSA (Atom Primitive inputEnv instruction)
open Isotope (Value)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open SeaOfNodes.Loop.LambdaSSA

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data} {σ : Type x}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {p : Program Op regs out} {code : Region (Primitive Op)}
variable (emitted : lower p = some code)
include emitted

theorem lower_hasType :
    code.HasType (Generic.inputContext regs) [Generic.packed [.value out]] := by
  obtain ⟨g, _, rfl⟩ := Option.map_eq_some_iff.mp emitted
  exact Generic.lower_hasType g

variable (m : Model.{u, v, w} Op) (input : Bank (regs := regs) m)

/-- Every finite evaluation of the emitted region has external exit zero,
the encoded source result and unchanged ambient state, and conversely. -/
theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Eval (instruction m) (inputEnv m input) code start label payload finish ↔
      ∃ result, (∃ budget, p.evalBackedges m budget input = some result) ∧ label = 0 ∧
        payload = Generic.packResult m (out := out) result ∧ finish = start := by
  obtain ⟨g, accepted, rfl⟩ := Option.map_eq_some_iff.mp emitted
  simpa only [Prune.returns_iff p (carriedMask p) accepted m input] using
    Generic.lower_eval_iff g m input start finish label payload

/-- Fuel counts header visits, so source budget b corresponds to exactly
b + 1 units of CFG fuel. This also preserves exhaustion. -/
theorem run_succ [DecidableEq Data] (budget : Nat) :
    Generic.Fuel.run m (inputEnv m input) (budget + 1) code =
      (p.evalBackedges m budget input).map (fun result => (0, Generic.packResult m (out := out) result)) := by
  obtain ⟨g, accepted, rfl⟩ := Option.map_eq_some_iff.mp emitted
  rw [Generic.Fuel.run_succ, Prune.eval_agrees p (carriedMask p) accepted m input]

theorem run_zero [DecidableEq Data] : Generic.Fuel.run m (inputEnv m input) 0 code = none := by
  obtain ⟨g, _, rfl⟩ := Option.map_eq_some_iff.mp emitted
  exact Generic.Fuel.run_zero g m input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA
