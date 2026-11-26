module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Denotation
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial.Correspondence

/-! # Partial observations of an emitted pruned quad loop -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial

open Diamond (Model ValueSort)
open Diamond.LambdaSSA (Atom Primitive inputEnv instruction)
open Isotope (Value)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open SeaOfNodes.Loop.LambdaSSA

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data} {σ : Type x}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable (m : Model.{u, v, w} Op) (input : Bank (regs := regs) m)
variable {p : Program Op regs out} {code : Region (Primitive Op)}
variable (start : σ)

/-- Membership is exactly finite region evaluation with the same exit
label, payload and final ambient state. -/
theorem mem_observe_iff_eval (result : Observation m σ) :
    result ∈ observe m input code start ↔
      Eval (instruction m) (inputEnv m input) code start result.1 result.2.1 result.2.2 :=
  Proofs.mem_observe_iff_eval m input start result

/-- Successful pruning and emission preserve and reflect the original
full-bank partial observation, packing the result at external exit zero
and retaining the initial ambient state. -/
theorem observe_eq (emitted : lower p = some code) :
    observe m input code start =
      (p.lower.denote m input).map (fun result => (0, Generic.packResult m (out := out) result, start)) :=
  Proofs.observe_eq m input start emitted

/-- Undefinedness requires exhaustion at every source backedge budget. -/
theorem observe_eq_none_iff (emitted : lower p = some code) :
    observe m input code start = Part.none ↔ ∀ budget, p.evalBackedges m budget input = none :=
  Proofs.observe_eq_none_iff m input start emitted

/-- The executable λSSA runner sees exactly the finite observations of
this emission, with the ambient state unchanged. -/
theorem mem_observe_iff_run [DecidableEq Data] (emitted : lower p = some code)
    (label : Nat) (payload : Value (Atom m)) (finish : σ) :
    (label, payload, finish) ∈ observe m input code start ↔
      (∃ fuel, Generic.Fuel.run m (inputEnv m input) fuel code = some (label, payload)) ∧ finish = start :=
  Proofs.mem_observe_iff_run m input start emitted label payload finish

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial
