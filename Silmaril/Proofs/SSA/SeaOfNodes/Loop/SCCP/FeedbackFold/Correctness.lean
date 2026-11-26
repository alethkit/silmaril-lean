module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Structure

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Proofs

open Diamond (Model Signature Ty Val ValueSort dataPorts)
open Diamond.SCCP (Fact TupleCovers)
open RVSDG (Port Tuple)
open ReturnFold (Literals)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out sort : ValueSort Data}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)} {literals : Literals m sort}
variable {port : Port (dataPorts carried) (.value sort)}
variable {rewritten : Graph Op inputs carried entrySigs (headerSigs ++ [[.value sort]]) out}
variable {entry : Tuple (Val m.value) (dataPorts inputs)}

attribute [local irreducible] SCCP.solve

theorem rewrite_ok_iff :
    rewrite m g input port literals = .ok rewritten ↔
      ∃ value, feedbackFact m g input port = .constant value ∧
        rewritten = withLiteral g port (literals.opcode value) := by
  unfold rewrite
  cases feedbackFact m g input port <;> simp [eq_comm]

private theorem feedbackFact_cover (covered : TupleCovers input entry)
    {via : Incoming} {count : Nat} {old next : Tuple (Val m.value) (dataPorts carried)}
    (arrived : Arrives m g entry via count old) (taken : g.step m entry old = .inr next) :
    (feedbackFact m g input port).Covers (next.get port) := by
  have oldCovered : BankCovers (SCCP.solve m g input).2.1 old :=
    (SCCP.solve_arrives m g covered arrived).2
  have marked := (SCCP.solve_arrives m g covered (.backedge arrived taken)).1
  have covers := SCCP.headerFeedback_cover g covered oldCovered port
  have actual : g.latch m .backedge (appendTuple old entry)
      (g.header.eval m (appendTuple old entry) PUnit.unit) = next := by
    dsimp only [Graph.step] at taken
    split at taken
    · exact Sum.inr.inj taken
    · cases taken
  unfold feedbackFact gate
  rw [ite_eq_left marked]
  exact actual ▸ covers

theorem step_eq (success : rewrite m g input port literals = .ok rewritten)
    (covered : TupleCovers input entry)
    {via : Incoming} {count : Nat} {old : Tuple (Val m.value) (dataPorts carried)}
    (arrived : Arrives m g entry via count old) :
    rewritten.step m entry old = g.step m entry old := by
  obtain ⟨value, known, rfl⟩ := rewrite_ok_iff.mp success
  erw [withLiteral_step, literals.run_opcode value]
  cases taken : g.step m entry old with
  | inl _ => rfl
  | inr next =>
    have cover := feedbackFact_cover (port := port) covered arrived taken
    rw [known] at cover
    change value = next.get port at cover
    change Sum.inr (Quads.write port value next) = Sum.inr next
    rw [cover, write_get]

theorem evalBackedges_eq (success : rewrite m g input port literals = .ok rewritten)
    (covered : TupleCovers input entry) (budget : Nat) :
    rewritten.evalBackedges m budget entry = g.evalBackedges m budget entry := by
  have initial : rewritten.initial m entry = g.initial m entry := by
    obtain ⟨_, _, rfl⟩ := rewrite_ok_iff.mp success
    rfl
  exact SCCP.evalBackedges_eq_of_steps rewritten initial (fun arrived => step_eq success covered arrived) budget

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Proofs
