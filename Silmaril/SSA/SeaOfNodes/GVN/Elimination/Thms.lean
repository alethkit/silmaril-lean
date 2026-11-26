module

public import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Elimination

open Diamond (Dataflow Model Signature Ty Val ValueSort)
open RVSDG (Locals Origin Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))} {out : ValueSort Data}
variable {flow : Dataflow Op args past sigs}
/-- Splitting an extended origin reads either its old wire or a port
of the appended result. -/
theorem read_splitOrigin {head : List (Ty Data)} {t : Ty Data}
    (wire : Origin args (past ++ [head]) t) (m : Model.{u,v,w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (next : Tuple (Val m.value) head) :
    (match splitOrigin head wire with
      | .inl prior => Diamond.read m prior entry locals
      | .inr port => next.get port) = Diamond.read m wire entry (locals.snoc next) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.read_splitOrigin m entry wire locals next

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- Every old wire has the same value after applying the returned routing.
This includes reads of the deleted producer and the final result wire. -/
theorem eliminate_sound (candidate representative : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out))
    (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) {result : Rewrite Op args past sigs}
    (accepted : eliminate? candidate representative replacement = some result) :
    Routing.Agrees result.route m entry (flow.eval m entry locals) (result.flow.eval m entry locals) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.eliminate_sound
    m entry candidate representative replacement locals accepted

/-- A successful rewrite removes exactly one producer. -/
theorem eliminate_size (candidate representative : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out)) {result : Rewrite Op args past sigs}
    (accepted : eliminate? candidate representative replacement = some result) :
    result.sigs'.length + 1 = sigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination.eliminate_size candidate representative replacement accepted

end Silmaril.SSA.SeaOfNodes.GVN.Elimination
