module

public import Silmaril.SSA.SeaOfNodes.GVN.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Soundness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN

open Diamond (Dataflow Model Signature Ty Val ValueSort)
open RVSDG (Locals Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))} {out : ValueSort Data}
variable {flow : Dataflow Op args past sigs}
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
