module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Thms

/-! A constant feedback operand whose join with the entry operand widens. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Example

open SCCP.Example (Byte word entry facts)
open ReturnFold (Refusal)
open ReturnFold.Example (Opcode model literals)

abbrev HeaderSigs : List (List (Diamond.Ty Unit)) := [[.value word]]

/-- Entry latches the start input. Feedback computes start plus one.
The external flag controls whether the loop returns or takes feedback. -/
def graph : Program Opcode [word, .predicate] () [] HeaderSigs word where
  preheader := .nil
  header := .cons (.original (.advance 1)) (.cons (.arg .head) .nil) .nil
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output ⟨0, by decide⟩ .head) .nil
  predicate := .arg (.tail .head)
  result := .arg (.tail (.tail .head))

def fold : Except Refusal (Program Opcode [word, .predicate] () [] (HeaderSigs ++ [[.value word]]) word) :=
  rewrite model graph (facts 0 .overdefined) .head literals

def feedbackProducer : Except Refusal (Option Nat) :=
  fold.map fun rewritten => ((rewritten.phiInputs .backedge).get .head).producer

def run (test : Bool) (budget : Nat) : Except Refusal (Option Nat) :=
  fold.map fun rewritten => (rewritten.evalBackedges model budget (entry 0 test)).map BitVec.toNat

def refusal (enabled : Bool) : Except Refusal (Option Nat) :=
  (rewrite model (ReturnFold.Example.graph 1) (facts 0 (.constant ⟨enabled⟩)) .head literals).map
    fun rewritten => ((rewritten.phiInputs .backedge).get .head).producer

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Example
