module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Correctness

/-! # Typing and finite returns of the linked λSSA CFG -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA

open Diamond.LambdaSSA (Atom Code Primitive encodeTuple initialContext inputEnv instruction)
open Arms.LambdaSSA (resultCode)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {inputs middle results : List (ValueSort Data)}
variable {firstSigs secondSigs : List (List (Diamond.Ty Data))}
/-- Link one packed exit to the entire input of the next closed stage. -/
theorem link_hasType {context exits : List (Code Data)} {first after : Region (Primitive Op)}
    (beforeTyped : first.HasType context [resultCode middle])
    (afterTyped : after.HasType (initialContext middle) exits) :
    (link middle first after).HasType context exits :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.link_hasType beforeTyped afterTyped

/-- When both stages have a finite exit-zero run with the same intermediate
tuple, their linked CFG has exactly the second observation. -/
theorem link_eval_iff (m : Model.{u,v,w} Op)
    {first after : Region (Primitive Op)} {captured : Env (Atom m)}
    {joined : Tuple (Val m.value) (dataPorts middle)} {result : Value (Atom m)}
    {start between expected : σ}
    (beforeRun : Semantics.Region.Eval (instruction m) captured first start 0 (encodeTuple m joined) between)
    (afterRun : Semantics.Region.Eval (instruction m) (inputEnv m joined) after between 0 result expected)
    (label : Nat) (payload : Value (Atom m)) (finish : σ) :
    Semantics.Region.Eval (instruction m) captured (link middle first after) start label payload finish ↔
      label = 0 ∧ payload = result ∧ finish = expected :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.link_eval_iff m beforeRun afterRun label payload finish

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
