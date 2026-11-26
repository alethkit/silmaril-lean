module

public import Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.LambdaSSA.Correctness

/-! # Typed block bindings, exact occurrences and lambda-SSA returns -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA

open RVSDG (Port)
open Diamond (ValueSort dataPorts sortValue)
open Diamond.LambdaSSA (Atom LayoutMatch encode encodeTuple inputEnv instruction)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {n : Nat} {σ : Type x}
variable {graph : Graph Op regs n} {source : Fin n}

/-- Each emitted operand names the register's actual reaching version at the predecessor. -/
theorem binding_incoming (edge : Edge graph source) {t : Diamond.Ty Data}
    (port : Port (dataPorts regs) t) :
    (boundOperand edge port).versions.incoming = (graph.versions source).get port :=
  Proofs.binding_incoming edge port

/-- The destination field binds either the inherited version or the placed Φ. -/
theorem binding_bound (edge : Edge graph source) {t : Diamond.Ty Data}
    (port : Port (dataPorts regs) t) :
    (boundOperand edge port).versions.bound = (boundOperand edge port).versions.incoming ∨
      (boundOperand edge port).versions.bound = .phi edge.target :=
  Proofs.binding_bound edge port

theorem lower_hasType (program : Program graph out) :
    (lower program).HasType (bankTypes regs) [returnCode out] :=
  Proofs.lower_hasType program

/-- The generated branch leaf keeps the full source occurrence, including its slot. -/
theorem selected_edge (program : Program graph out) (m : Diamond.Model.{u, v, w} Op)
    (bank : Bank m regs) (source : Fin n) :
    occurrenceEdge program (selectedOccurrence program m bank source) =
      match (program.terminator source).eval m bank with
      | .inl _ => none
      | .inr edge => some edge :=
  Proofs.selected_edge program m bank source

/-- Parallel arms with different source slots are different generated leaves. -/
theorem selected_distinct (program : Program graph out) (m : Diamond.Model.{u, v, w} Op)
    (leftBank rightBank : Bank m regs) (left right : Edge graph source)
    (leftTaken : (program.terminator source).eval m leftBank = .inr left)
    (rightTaken : (program.terminator source).eval m rightBank = .inr right)
    (differentSlots : left.slot ≠ right.slot) :
    selectedOccurrence program m leftBank source ≠ selectedOccurrence program m rightBank source :=
  Proofs.selected_distinct program m leftBank rightBank left right leftTaken rightTaken differentSlots

/-- The real emitted block executes its ordered producers and transfers the
typed payload selected by its source terminator on the updated bank. -/
theorem block_eval (program : Program graph out) (m : Diamond.Model.{u, v, w} Op)
    (entry : Bank m regs) (captured : Env (Atom m)) (start : σ) :
    let bank := (graph.body source).eval m entry
    let step := (program.terminator source).eval m bank
    Semantics.Region.Eval (instruction m) (extend captured (encodeTuple m entry))
      (blocks program source) start (stepLabel (m := m) step) (stepPayload m bank step) start :=
  Proofs.block_eval m entry program captured start

/-- The selected target column latches the bank computed by the source Φ plan
for that exact incoming occurrence, even if its label is shared by another arm. -/
theorem selected_packet (program : Program graph out) (m : Diamond.Model.{u, v, w} Op)
    (input entry : Bank m regs) (path : Path graph source) (edge : Edge graph source)
    {env : Env (Atom m)}
    (matched : LayoutMatch m (finalLayout graph source) env entry
      ((transfer graph source).flow.eval m entry PUnit.unit))
    (same : (graph.body source).eval m entry = path.eval m input)
    (taken : (program.terminator source).eval m ((graph.body source).eval m entry) = .inr edge) :
    let occurrence := selectedOccurrence program m ((graph.body source).eval m entry) source
    occurrenceEdge program occurrence = some edge ∧ occurrence.target = edge.target.val ∧
      ∃ bank, headerBank m input edge path = some bank ∧
        PhiView.latch (phiView program) occurrence (leafEnv occurrence.successor env) =
          encodeTuple m bank :=
  Proofs.selected_packet program m input entry path edge matched same taken

/-- All finite lambda-SSA observations are precisely external exit zero, the
source runner's packed return, and the unchanged state. -/
theorem lower_eval_iff (program : Program graph out) (m : Diamond.Model.{u, v, w} Op)
    (input : Bank m regs) (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m input) (lower program) start label payload finish ↔
      label = 0 ∧ payload = .pair (encode m (program.run m input).result) .unit ∧ finish = start :=
  Proofs.lower_eval_iff program m input start finish label payload

theorem returns_iff (program : Program graph out) (m : Diamond.Model.{u, v, w} Op)
    (input : Bank m regs) (start : σ) (result : sortValue m.value out) :
    Semantics.Region.Eval (instruction m) (inputEnv m input) (lower program) start 0
        (.pair (encode m result) .unit) start ↔
      (program.run m input).result = result :=
  Proofs.returns_iff program m input start result

end Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA
