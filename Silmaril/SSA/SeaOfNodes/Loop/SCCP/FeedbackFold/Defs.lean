module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Defs

/-! Replace one proved-constant operand in the native backedge column. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Port Tuple)
open ReturnFold (Literals Refusal appendLiteral)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out sort : ValueSort Data}

/-- Append one literal and use it only at the selected backedge operand.
The entry column is unchanged, and all other wires follow their origins. -/
def withLiteral (g : Graph Op inputs carried entrySigs headerSigs out)
    (port : Port (dataPorts carried) (.value sort)) (literal : Op [] sort) :
    Graph Op inputs carried entrySigs (headerSigs ++ [[.value sort]]) out :=
  let added := appendLiteral literal g.header
  { preheader := g.preheader
    header := added.flow
    phiInputs
      | .entry => g.phiInputs .entry
      | .backedge => Quads.write port added.result ((g.phiInputs .backedge).map (fun _ wire => added.keep wire))
    predicate := added.keep g.predicate
    result := added.keep g.result }

variable (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts carried)]
variable (g : Graph Op inputs carried entrySigs headerSigs out) (input : Tuple (Fact m.value) (dataPorts inputs))

/-- The fact belongs to the feedback operand, before the join with the
entry operand. An unmarked backedge supplies no evidence. -/
def feedbackFact (port : Port (dataPorts carried) (.value sort)) : Fact m.value (.value sort) :=
  let solution := SCCP.solve m g input
  gate solution.1 (incomingIndex .backedge) ((bankTuple (headerFacts m g input solution.2.1).feedback).get port)

def rewrite (port : Port (dataPorts carried) (.value sort)) (literals : Literals m sort) :
    Except Refusal (Graph Op inputs carried entrySigs (headerSigs ++ [[.value sort]]) out) :=
  match feedbackFact m g input port with
  | .constant value => .ok (withLiteral g port (literals.opcode value))
  | .bottom => .error .unseen
  | .overdefined => .error .overdefined

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold
