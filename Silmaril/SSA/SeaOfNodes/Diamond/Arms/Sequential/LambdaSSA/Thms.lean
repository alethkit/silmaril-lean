module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Correctness

/-! # Typing and finite returns of the linked λSSA CFG -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA

open Diamond.LambdaSSA (Atom encodeTuple initialContext inputEnv instruction)
open Arms.LambdaSSA (resultCode)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {inputs middle results : List (ValueSort Data)}
variable {firstSigs secondSigs : List (List (Diamond.Ty Data))}
variable (g : Graph Op inputs middle results firstSigs secondSigs)

theorem lower_hasType : (lower g).HasType (initialContext inputs) [resultCode results] :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.lower_hasType g

/-- A projection name may recur at a later diamond, but its occurrence belongs
to a different CFG scope. -/
theorem edge_stage_distinct (firstSlot secondSlot : Slot) :
    edge g .first firstSlot ≠ edge g .second secondSlot :=
  fun same => by cases same

variable (m : Model.{u,v,w} Op)

/-- The link block binds the packet once. The second diamond's finite
observation depends on its fields, with the captured context left unused. -/
theorem continuation_eval (joined : Tuple (Val m.value) (dataPorts middle)) (captured : Env (Atom m))
    (start : σ) :
    Semantics.Region.Eval (instruction m) (extend captured (encodeTuple m joined)) (continuation g)
      start 0 (encodeTuple m (g.second.denote m joined)) start :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.continuation_eval m g joined captured start

variable (entry : Tuple (Val m.value) (dataPorts inputs))

/-- Every finite target run exits at zero with the packed source result and
the same ambient state. -/
theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start label payload finish ↔
      label = 0 ∧ payload = encodeTuple m (g.denote m entry) ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.lower_eval_iff m g entry start finish label payload

/-- Actual CFG execution preserves and reflects each finite source return. -/
theorem returns_iff (start : σ) (result : Tuple (Val m.value) (dataPorts results)) :
    g.Returns m entry result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start
        0 (encodeTuple m result) start :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.returns_iff m g entry start result

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA
