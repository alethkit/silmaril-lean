module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Correctness

/-! The constant return rewrite preserves all covered finite observations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
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
