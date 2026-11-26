module

public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.Correctness

/-! # Typing, φ edge agreement and finite return correspondence -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA

open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Data : Type u} {Op : Signature.{u,v} Data} {σ : Type x}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}
variable (g : Graph Op inputs sigs out)

/-- The scheduled region has the original inputs and one typed external exit. -/
theorem lower_hasType :
    (lower g).HasType (initialContext inputs) [sortCode out] :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.lower_hasType g

theorem projections_distinct : projectionEdge g .onTrue ≠ projectionEdge g .onFalse :=
  fun equal => by cases equal

/-- Reading back a Region predecessor slot through the φ view emits its
operand's branch into the sole join, in either predecessor order. -/
theorem edge_branch (slot : Slot) :
    (phiView g).table.branch (edge g slot) = .br 0 (PhiView.packTerm (slotArguments g slot)) :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.edge_branch g slot

variable (m : Model.{u,v,w} Op)

/-- The unit case binder shifts the variable index. Latching still reads the
operand from the environment at the end of the producer schedule. -/
theorem edge_latch (slot : Slot) (old : Env (Atom m)) :
    PhiView.latch (phiView g) (edge g slot) (Semantics.extend old .unit) =
      .pair (old ((finalLayout g).resolve (g.phi.operand slot)).val) .unit :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.edge_latch m g slot old

/-- The selected canonical branch transfers exactly the latched operand to
the join and leaves state unchanged. -/
theorem edge_transfer_iff (slot : Slot) (old : Env (Atom m)) (start finish : σ)
    (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (Semantics.extend old .unit)
        (.br (edge g slot).target (edge g slot).argument) start label payload finish ↔
      label = 0 ∧ payload = .pair (old ((finalLayout g).resolve (g.phi.operand slot)).val) .unit ∧
        finish = start :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.edge_transfer_iff m g slot old start finish label payload

/-- All finite observations of the emitted region are characterized by the
source denotation, external exit zero and unchanged ambient state. -/
theorem lower_eval_iff (entry : Tuple (Val m.value) (dataPorts inputs))
    (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start label payload finish ↔
      label = 0 ∧ payload = encode m (g.denote m entry) ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.lower_eval_iff m g entry start finish label payload

/-- The original graph return relation and actual λSSA finite return agree. -/
theorem returns_iff (entry : Tuple (Val m.value) (dataPorts inputs)) (start : σ)
    (result : sortValue m.value out) :
    g.Returns m entry result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start 0 (encode m result) start :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.returns_iff m g entry start result

end Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
