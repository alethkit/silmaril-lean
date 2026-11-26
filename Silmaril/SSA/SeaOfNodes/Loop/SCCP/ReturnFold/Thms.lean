module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Correctness
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Structure

/-! The constant return rewrite preserves all covered finite observations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold

open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers)
open RVSDG (Locals Origin Tuple Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op}

section Append

variable {args ports : List (Ty Data)} {past sigs target : List (List (Ty Data))}

/-- Appending a nullary producer preserves every embedded read, and its
new wire reads the nullary operation's value. -/
theorem append_reads (literal : Op [] out) (flow : Dataflow Op args past sigs)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    let added := appendLiteral literal flow
    let before := flow.eval m entry locals
    let after := added.flow.eval m entry locals
    (∀ (t : Ty Data) (wire : Origin args (extend past sigs) t),
      Diamond.read m (added.keep wire) entry after = Diamond.read m wire entry before) ∧
      Diamond.read m added.result entry after = m.run literal .nil :=
  Proofs.append_reads literal flow entry locals

theorem read_mapped (wires : Wires args past ports)
    (route : ∀ (t : Ty Data), Origin args past t → Origin args target t)
    (entry : Tuple (Val m.value) args)
    (before : Locals (Val m.value) past) (after : Locals (Val m.value) target)
    (same : ∀ t wire, Diamond.read m (route t wire) entry after = Diamond.read m wire entry before) :
    Wires.read (wires.map route) entry after = wires.read entry before :=
  Proofs.read_mapped wires route entry before after same

end Append

variable [BankDecidableEq m.value (dataPorts carried)]
variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)} {literals : Literals m out}
variable {rewritten : Graph Op inputs carried entrySigs (headerSigs ++ [[.value out]]) out}

theorem rewrite_ok_iff :
    rewrite m g input literals = .ok rewritten ↔
      ∃ value, (SCCP.solve m g input).2.2 = .constant value ∧
        rewritten = withLiteral g (literals.opcode value) :=
  Proofs.rewrite_ok_iff

theorem rewrite_error_iff (reason : Refusal) :
    rewrite m g input literals = .error reason ↔
      match reason with
      | .unseen => (SCCP.solve m g input).2.2 = .bottom
      | .overdefined => (SCCP.solve m g input).2.2 = .overdefined :=
  Proofs.rewrite_error_iff reason

/-- The original guard is preserved at every native header activation. -/
theorem guard_eq (success : rewrite m g input literals = .ok rewritten)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (old : Tuple (Val m.value) (dataPorts carried)) :
    let args := appendTuple old entry
    Diamond.read m rewritten.predicate args (rewritten.header.eval m args PUnit.unit) =
      Diamond.read m g.predicate args (g.header.eval m args PUnit.unit) :=
  Proofs.guard_eq success entry old

variable {entry : Tuple (Val m.value) (dataPorts inputs)}

/-- Exact agreement for every native backedge budget and covered entry. -/
theorem evalBackedges_eq (success : rewrite m g input literals = .ok rewritten)
    (covered : TupleCovers input entry) (budget : Nat) :
    rewritten.evalBackedges m budget entry = g.evalBackedges m budget entry :=
  Proofs.evalBackedges_eq success covered budget

theorem returns_iff (success : rewrite m g input literals = .ok rewritten)
    (covered : TupleCovers input entry) (result : sortValue m.value out) :
    rewritten.Returns m entry result ↔ g.Returns m entry result := by
  simp only [Graph.returns_iff_evalBackedges, evalBackedges_eq success covered]

theorem noFiniteReturn_iff (success : rewrite m g input literals = .ok rewritten)
    (covered : TupleCovers input entry) :
    (¬ ∃ result, rewritten.Returns m entry result) ↔ ¬ ∃ result, g.Returns m entry result := by
  simp only [returns_iff success covered]

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold
