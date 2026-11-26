module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Structure

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Proofs

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

attribute [local irreducible] SCCP.solve

theorem rewrite_ok_iff :
    rewrite m g input literals = .ok rewritten ↔
      ∃ value, (SCCP.solve m g input).2.2 = .constant value ∧
        rewritten = withLiteral g (literals.opcode value) := by
  unfold rewrite
  cases (SCCP.solve m g input).2.2 <;> simp [eq_comm]

theorem rewrite_error_iff (reason : Refusal) :
    rewrite m g input literals = .error reason ↔
      match reason with
      | .unseen => (SCCP.solve m g input).2.2 = .bottom
      | .overdefined => (SCCP.solve m g input).2.2 = .overdefined := by
  unfold rewrite
  cases reason <;> cases (SCCP.solve m g input).2.2 <;> simp

theorem guard_eq (success : rewrite m g input literals = .ok rewritten)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (old : Tuple (Val m.value) (dataPorts carried)) :
    let args := appendTuple old entry
    Diamond.read m rewritten.predicate args (rewritten.header.eval m args PUnit.unit) =
      Diamond.read m g.predicate args (g.header.eval m args PUnit.unit) := by
  obtain ⟨_, _, rfl⟩ := rewrite_ok_iff.mp success
  exact withLiteral_guard g _ entry old

theorem evalBackedges_eq (success : rewrite m g input literals = .ok rewritten)
    {entry : Tuple (Val m.value) (dataPorts inputs)} (covered : TupleCovers input entry) (budget : Nat) :
    rewritten.evalBackedges m budget entry = g.evalBackedges m budget entry := by
  obtain ⟨value, known, rfl⟩ := rewrite_ok_iff.mp success
  have mapped : (withLiteral g (literals.opcode value)).evalBackedges m budget entry =
      (g.evalBackedges m budget entry).map (fun _ => m.run (literals.opcode value) .nil) :=
    withLiteral_evalFrom g (literals.opcode value) entry budget (g.initial m entry)
  rw [mapped, literals.run_opcode]
  cases observed : g.evalBackedges m budget entry with
  | none => rfl
  | some result =>
    have returns := (g.returns_iff_evalBackedges m entry result).mpr ⟨budget, observed⟩
    have cover := (SCCP.solve_returns m g covered returns).2
    rw [known] at cover
    change value = result at cover
    rw [cover]
    rfl

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Proofs
