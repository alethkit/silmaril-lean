module

public import Silmaril.SSA.Peggy.EPEG.Selection.Defs
public import Silmaril.SSA.Peggy.EPEG.Thms
import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.Peggy.EPEG.Selection

public section

namespace Silmaril.SSA.Peggy.EPEG.Selection

open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : PEG.InstructionSet.{u,v} Data}
variable {params results : List (PEG.Ty Data)} {n n' l : Nat}
variable {source : PEG.Graph P params results n l} {target : PEG.Graph P params results n' l}
variable {m : PEG.Interpretation.{u,v,x} P} {values : source.Valuation m}
variable {env : Tuple m.Value params} {classes : Classes n} {sel : Selection source target}

/-- Comparing class-labelled ordered edges of the common rows establishes all
candidate equations, including feedback and unbounded sample demands. -/
theorem rows_solve (rows : ∀ v, Row sel v) (check : checkRows rows classes = true)
    (solves : source.Solves m env values) (valid : classes.Valid values) :
    target.Solves m env (sel.inherit values) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.rows_solve rows check solves valid

/-- Separate checks establish admission, root alignment, and the row equations. -/
theorem observe_sound_of_rows (wf : WellFounded source.Demand)
    (valid : classes.Valid (source.denote m env wf))
    (boundary : sel.check classes = true) (rows : ∀ v, Row sel v)
    (check : checkRows rows classes = true) (i : PEG.Index l) :
    source.observe m (source.denote m env wf) i =
      target.observe m (target.denote m env (sel.demandWellFounded boundary)) i :=
  sel.observe_sound wf valid boundary (rows_solve rows check (source.denote_solves m env wf) valid) i

end Silmaril.SSA.Peggy.EPEG.Selection
