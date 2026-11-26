module

public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.Correctness

/-! # Typing, φ edge agreement and finite return correspondence -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA

open RVSDG (Locals Origin Port Tuple extend)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Data : Type u} {Op : Signature.{u,v} Data} {σ : Type x}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}
variable (g : Graph Op inputs sigs out)

section Schedule

variable {args : List (Ty Data)} {past : List (List (Ty Data))}
variable {context labels : List (Code Data)}

theorem schedule_typed (flow : Dataflow Op args past sigs)
    (layout : Layout args past context) {tail : Region (Primitive Op)}
    (typed : tail.HasType (scheduledContext context sigs) labels) :
    (schedule flow layout tail).HasType context labels :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.schedule_typed flow layout typed

theorem tuple_get_map {T : Type u} {F : T → Type v} {G : T → Type w}
    {ports : List T} {t : T} (f : ∀ t, F t → G t) (xs : Tuple F ports) (p : Port ports t) :
    (xs.map f).get p = f t (xs.get p) :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.get_map f xs p

variable (m : Model.{u,v,w} Op)

theorem encode_injective {sort : ValueSort Data} :
    Function.Injective (encode m (sort := sort)) :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.encode_injective m

/-- Packed tuples distinguish all source vectors of data and predicate sorts. -/
theorem encodeTuple_injective (sorts : List (ValueSort Data)) :
    Function.Injective (encodeTuple m (ports := dataPorts sorts)) :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.encodeTuple_injective m sorts

theorem instruction_deterministic : Semantics.InstrDeterministic (instruction m (σ := σ)) :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.instruction_deterministic m

theorem inputRefs_match {ports : List (Ty Data)} (values : Tuple (Val m.value) ports) :
    TupleMatch m (inputEnv m values) (inputRefs ports) values :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.inputRefs_match m values

theorem LayoutMatch.resolve {layout : Layout args past context}
    {env : Env (Atom m)} {entry : Tuple (Val m.value) args} {locals : Locals (Val m.value) past}
    (matched : LayoutMatch m layout env entry locals) {port : Ty Data}
    (origin : Origin args past port) :
    env (layout.resolve origin).val = encodePort m (read m origin entry locals) :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.LayoutMatch.resolve m matched origin

/-- Each producer becomes one let. The continuation receives an environment
that agrees with source wire reads after the entire pure producer table. -/
theorem schedule_eval (flow : Dataflow Op args past sigs)
    {layout : Layout args past context} {env : Env (Atom m)}
    {entry : Tuple (Val m.value) args} {locals : Locals (Val m.value) past}
    (matched : LayoutMatch m layout env entry locals) {tail : Region (Primitive Op)}
    {label : Nat} {payload : Value (Atom m)} (start : σ)
    (runTail : ∀ finalEnv, LayoutMatch m (scheduleLayout flow layout) finalEnv entry
        (flow.eval m entry locals) →
      Semantics.Region.Eval (instruction m) finalEnv tail start label payload start) :
    Semantics.Region.Eval (instruction m) env (schedule flow layout tail) start label payload start :=
  Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.schedule_eval m flow matched start runTail

end Schedule

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
