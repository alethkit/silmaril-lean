module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Thms
public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
public import Silmaril.SSA.PhiView.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Correctness

/-! # Typing, occurrence-indexed transfers and finite returns -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA

open Diamond.LambdaSSA (Atom LayoutMatch encodeTuple initialContext inputEnv instruction)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {inputs results : List (ValueSort Data)} {sigs : List (List (Diamond.Ty Data))}
variable (g : Graph Op inputs sigs results)

theorem lower_hasType : (lower g).HasType (initialContext inputs) [resultCode results] :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.lower_hasType g

theorem incoming_distinct : incoming g .onTrue ≠ incoming g .onFalse :=
  fun same => by cases same

theorem edge_branch (slot : Slot) :
    (phiView g).table.branch (edge g slot) =
      .br 2 (PhiView.packTerm (armArgs g (g.merge.predecessor slot))) :=
  PhiView.branch_eq (phiView g) (edge g slot)

variable (m : Model.{u,v,w} Op)
variable (entry : Tuple (Val m.value) (dataPorts inputs))

/-- A Region predecessor slot latches all its result wires in the matching
arm's final environment, before the join binds the tuple. -/
theorem edge_latch (slot : Slot) {env : Env (Atom m)}
    (matched : LayoutMatch m (armLayout g (g.merge.predecessor slot)) env entry
      ((selectedArm g (g.merge.predecessor slot)).dataflow.eval m entry
        (g.shared.eval m entry PUnit.unit))) :
    PhiView.latch (phiView g) (edge g slot) env =
      encodeTuple m ((g.arms slot).eval m entry (g.shared.eval m entry PUnit.unit)) :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.edge_latch m entry slot matched

/-- An actual incoming jump reads the whole tuple from one predecessor
column in the old environment. The jump leaves ambient state unchanged. -/
theorem edge_transfer_iff (slot : Slot) {env : Env (Atom m)}
    (matched : LayoutMatch m (armLayout g (g.merge.predecessor slot)) env entry
      ((selectedArm g (g.merge.predecessor slot)).dataflow.eval m entry
        (g.shared.eval m entry PUnit.unit)))
    (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) env (.br (edge g slot).target (edge g slot).argument)
        start label payload finish ↔
      label = 2 ∧ payload = encodeTuple m ((g.arms slot).eval m entry
        (g.shared.eval m entry PUnit.unit)) ∧ finish = start := by
  rw [PhiView.latch_eq_transfer (instruction m) (phiView g), edge_latch g m entry slot matched]
  rfl

/-- From the captured prefix environment the selected arm computes its
output vector and transfers it to the join at label two. -/
theorem arm_eval (p : Projection) {env : Env (Atom m)}
    (matched : LayoutMatch m (sharedLayout g) env entry (g.shared.eval m entry PUnit.unit))
    (start : σ) :
    Semantics.Region.Eval (instruction m) (Semantics.extend env .unit) (armBlock g p) start
      2 (encodeTuple m ((selectedArm g p).eval m entry (g.shared.eval m entry PUnit.unit))) start :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.arm_eval m entry p matched start

/-- Starting the emitted arm at a Region predecessor slot has exactly one
join observation. Every component belongs to that same occurrence. -/
theorem arm_transfer_iff (slot : Slot) {env : Env (Atom m)}
    (matched : LayoutMatch m (sharedLayout g) env entry (g.shared.eval m entry PUnit.unit))
    (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (Semantics.extend env .unit) (armBlock g (g.merge.predecessor slot))
        start label payload finish ↔
      label = (edge g slot).target ∧ payload = encodeTuple m ((g.arms slot).eval m entry
        (g.shared.eval m entry PUnit.unit)) ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.arm_transfer_iff m entry slot matched start finish label payload

/-- The only finite observations are external exit zero, the packed source
result vector and unchanged ambient state. -/
theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start label payload finish ↔
      label = 0 ∧ payload = encodeTuple m (g.denote m entry) ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.lower_eval_iff m entry start finish label payload

theorem returns_iff (start : σ) (result : Tuple (Val m.value) (dataPorts results)) :
    g.Returns m entry result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start
        0 (encodeTuple m result) start :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.returns_iff m entry start result

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA
