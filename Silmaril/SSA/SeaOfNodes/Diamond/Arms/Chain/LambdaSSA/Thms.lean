module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA.Correctness

/-! # Typing, join occurrences and finite returns of the folded CFG -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA

open Diamond.LambdaSSA (Atom encodeTuple initialContext inputEnv instruction)
open Arms.LambdaSSA (resultCode)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

universe u v w x

variable {Data : Type u} {Op : Signature.{u,v} Data} {σ : Type x}
variable {inputs results : List (ValueSort Data)}
variable (chain : Chain Op inputs results)

theorem lower_hasType : (lower chain).HasType (initialContext inputs) [resultCode results] :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA.lower_hasType chain

theorem edge_stage (stage : Fin chain.length) (slot : Slot) :
    (edge chain stage slot).source.1 = stage :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA.edge_stage chain stage slot

/-- Edges from different CFG stages remain distinct even when they have
the same projection and local destination. -/
theorem edges_from_distinct_stages {i j : Fin chain.length} (different : i ≠ j) (a b : Slot) :
    edge chain i a ≠ edge chain j b := by
  intro same
  apply different
  simpa only [edge_stage] using congrArg (fun edge => edge.source.1) same

variable (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) (dataPorts inputs))

/-- Every finite target observation has external label zero, the packed
source output and unchanged ambient state. Includes the empty chain. -/
theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower chain) start label payload finish ↔
      label = 0 ∧ payload = encodeTuple m (chain.denote m entry) ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA.lower_eval_iff m chain entry start finish label payload

/-- Actual CFG execution preserves and reflects every typed source return. -/
theorem returns_iff (start : σ) (result : Tuple (Val m.value) (dataPorts results)) :
    chain.Returns m entry result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower chain) start
        0 (encodeTuple m result) start :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA.returns_iff m chain entry start result

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA
