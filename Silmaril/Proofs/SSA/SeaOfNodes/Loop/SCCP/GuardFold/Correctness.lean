module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Structure

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Proofs

open Diamond (Model Signature Ty Val ValueSort dataPorts)
open Diamond.SCCP (Fact TupleCovers)
open RVSDG (Tuple)
open ReturnFold (Literals Refusal)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)} {literals : Literals m .predicate}
variable {rewritten : Graph Op inputs carried entrySigs (headerSigs ++ [[.value .predicate]]) out}
variable {entry : Tuple (Val m.value) (dataPorts inputs)}

attribute [local irreducible] SCCP.solve

theorem rewrite_ok_iff :
    rewrite m g input literals = .ok rewritten ↔
      ∃ test : Bool, guardFact m g input = .constant ⟨test⟩ ∧
        rewritten = withLiteral g (literals.opcode ⟨test⟩) := by
  unfold rewrite
  cases guardFact m g input with
  | bottom => simp
  | overdefined => simp
  | constant test => cases test with | up test => simp [eq_comm]

theorem rewrite_error_iff (reason : Refusal) :
    rewrite m g input literals = .error reason ↔
      match reason with
      | .unseen => guardFact m g input = .bottom
      | .overdefined => guardFact m g input = .overdefined := by
  unfold rewrite
  cases reason <;> cases guardFact m g input <;> simp

theorem executable_eq :
    (SCCP.solve m g input).1 = insert (incomingIndex .entry) (successors (guardFact m g input)) := by
  have fixed : control (SCCP.solve m g input).1 (guardFact m g input) = (SCCP.solve m g input).1 :=
    congrArg Prod.fst (SCCP.solve_fixed m g input)
  have entered : incomingIndex .entry ∈ (SCCP.solve m g input).1 := by
    rw [← fixed]
    simp [control]
  rw [control, ite_eq_left entered] at fixed
  exact fixed.symm

theorem step_eq (success : rewrite m g input literals = .ok rewritten) (covered : TupleCovers input entry)
    {via : Incoming} {count : Nat} {old : Tuple (Val m.value) (dataPorts carried)}
    (arrived : Arrives m g entry via count old) :
    rewritten.step m entry old = g.step m entry old := by
  obtain ⟨test, known, rfl⟩ := rewrite_ok_iff.mp success
  let args := appendTuple old entry
  let locals := g.header.eval m args PUnit.unit
  have bank : BankCovers (SCCP.solve m g input).2.1 old := (SCCP.solve_arrives m g covered arrived).2
  have guard : (guardFact m g input).Covers (Diamond.read m g.predicate args locals) :=
    SCCP.headerGuard_cover g covered bank
  rw [known] at guard
  have test_eq : test = (Diamond.read m g.predicate args locals).down := congrArg ULift.down guard
  erw [withLiteral_step, literals.run_opcode ⟨test⟩]
  change (if test then Sum.inr (g.latch m .backedge args locals)
      else Sum.inl (Diamond.read m g.result args locals)) = g.step m entry old
  rw [test_eq]
  rfl

theorem evalBackedges_eq (success : rewrite m g input literals = .ok rewritten)
    (covered : TupleCovers input entry) (budget : Nat) :
    rewritten.evalBackedges m budget entry = g.evalBackedges m budget entry := by
  have initial : rewritten.initial m entry = g.initial m entry := by
    obtain ⟨_, _, rfl⟩ := rewrite_ok_iff.mp success
    rfl
  exact SCCP.evalBackedges_eq_of_steps rewritten initial (fun arrived => step_eq success covered arrived) budget

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Proofs
