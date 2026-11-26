module

public import Silmaril.SSA.SeaOfNodes.GVN.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Soundness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN

open Diamond (Dataflow Model Signature Ty Val ValueSort)
open RVSDG (Locals Origin Port Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))} {out : ValueSort Data}
variable {flow : Dataflow Op args past sigs}

/-- Appending a binding preserves the value of each earlier wire. -/
theorem read_weaken {head : List (Ty Data)} {t : Ty Data} (wire : Origin args past t)
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) (next : Tuple (Val m.value) head) :
    Diamond.read m (weaken head wire) entry (locals.snoc next) = Diamond.read m wire entry locals :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.read_weaken m entry wire locals next

/-- The new result wire reads the corresponding port of the appended value. -/
theorem read_newest {head : List (Ty Data)} {t : Ty Data} (port : Port head t)
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) (next : Tuple (Val m.value) head) :
    Diamond.read m (newest port) entry (locals.snoc next) = next.get port :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.read_newest m entry port locals next

/-- A wire from the initial scope reads the same value after the suffix runs. -/
theorem read_keepOrigin {t : Ty Data} (flow : Dataflow Op args past sigs) (wire : Origin args past t)
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    Diamond.read m (keepOrigin flow wire) entry (flow.eval m entry locals) =
      Diamond.read m wire entry locals :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.read_keep m entry flow wire locals

/-- In the final environment, a producer reads its opcode applied to
its ordered operand wires, interpreted in that same environment. -/
theorem Producer.read_key (ref : Producer flow out)
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    let final := flow.eval m entry locals
    Diamond.read m ref.origin entry final = m.run ref.key.opcode (ref.key.operands.read entry final) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.read_producer_key m entry ref locals

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- An accepted representative produces the same typed value in every
pure total model and for every assignment at the table's boundary. -/
theorem checkRepresentative_sound (candidate representative : Producer flow out)
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (accepted : checkRepresentative candidate representative = true) :
    Diamond.read m candidate.origin entry (flow.eval m entry locals) =
      Diamond.read m representative.origin entry (flow.eval m entry locals) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.checkRepresentative_sound m entry candidate representative locals accepted

/-- Redirecting one result wire preserves the returned value of the same table. -/
theorem redirectResult_read (candidate representative : Producer flow out)
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    Diamond.read m (redirectResult candidate representative) entry (flow.eval m entry locals) =
      Diamond.read m candidate.origin entry (flow.eval m entry locals) := by
  unfold redirectResult
  split
  · exact (checkRepresentative_sound candidate representative m entry locals ‹_›).symm
  · rfl

end Silmaril.SSA.SeaOfNodes.GVN
