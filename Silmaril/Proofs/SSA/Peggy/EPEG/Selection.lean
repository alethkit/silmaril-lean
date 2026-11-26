module

public import Silmaril.SSA.Peggy.EPEG.Selection.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Sound

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG

open Silmaril.SSA
open Silmaril.SSA.Peggy.EPEG
open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : PEG.InstructionSet.{u,v} Data}
variable {params results : List (PEG.Ty Data)} {n n' l : Nat}
variable {source : PEG.Graph P params results n l} {target : PEG.Graph P params results n' l}
variable {m : PEG.Interpretation.{u,v,x} P} {values : source.Valuation m}
variable {env : Tuple m.Value params} {classes : Classes n} {sel : Selection source target}

theorem rows_solve (rows : ∀ v, Selection.Row sel v)
    (check : Selection.checkRows rows classes = true)
    (solves : source.Solves m env values) (valid : classes.Valid values) :
    target.Solves m env (sel.inherit values) := by
  rintro ⟨v, idx⟩
  let row := rows v
  let rep := sel.representative v
  have checked := List.all_eq_true.mp check v (List.mem_finRange v)
  have inherited : HEq (sel.inherit values (v, idx)) (values (rep.id, idx)) := read_heq rep _
  have lhs := inherited.trans ((heq_of_eq (solves (rep.id, idx))).trans
    (nodeValue_heq (values := values) (env := env) rep.typed row.sourceNode idx))
  have rhs : nodeValue (PEG.Node.ofLabel row.label row.sourceArgs) values env idx =
      target.equation m env (sel.inherit values) (v, idx) := by
    change _ = nodeValue (target.node v) (sel.inherit values) env idx
    rw [row.targetNode]
    unfold nodeValue
    apply congrArg (row.label.interpret m env idx)
    funext slot j admissible
    rw [read_sourceRef]
    have edge := List.all_eq_true.mp checked slot (List.mem_finRange slot)
    exact read_eq j (valid _ _ (beq_iff_eq.mp edge))
  exact eq_of_heq (lhs.trans (heq_of_eq rhs))

end Silmaril.Proofs.SSA.Peggy.EPEG
