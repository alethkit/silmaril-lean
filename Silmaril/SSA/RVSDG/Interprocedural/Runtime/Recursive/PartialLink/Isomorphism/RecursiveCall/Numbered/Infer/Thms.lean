module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Infer.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Check.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Infer.Map

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Local (Renaming)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S} [DecidableEq (Ty V S)]
variable {m : Machine.{u, v, w} Op}
variable {args outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
variable {keys : OpcodeCode (Instruction Op)} [DecidableEq keys.Key]

/-- The inferred candidate assigns each paired position and retains its
child maps at the original left vertex and arm indices. -/
theorem completeRows_assigned {rows : List RowPair} {map : Renaming}
    (completed : completeRows rows = some map) {row : RowPair} (present : row ∈ rows) :
    map.vertices row.left = row.right ∧ ∀ arm, map.child row.left arm = row.children[arm]?.getD .identity :=
  Proofs.completeRows_assigned completed present

/-- Any map accepted by the supplied-map checker agrees with the inferred
candidate on all active row positions of the checked region. This can be
applied separately to each child region with its own map. -/
theorem check_agrees_on_rows {left : Graph Op args [] sigsL outs}
    {right : Graph Op args [] sigsR outs} {map : Renaming} {rows : List RowPair}
    (aligned : alignRows (termSize left.toTerm + termSize right.toTerm) left.toTerm right.toTerm = some rows)
    (accepted : (check keys map left right).isSome = true) :
    ∀ row ∈ rows, map.vertices row.left = row.right :=
  Proofs.scan_assigned _ map _ _ aligned (by simpa only [check, Option.isSome_map] using accepted)

/-- Any successful inference carries the ordered certificate for the
actual input graphs. The existing reifier turns it into the schedule. -/
theorem infer_sound {left : Graph Op args [] sigsL outs} {right : Graph Op args [] sigsR outs}
    (accepted : (infer keys left right).isSome = true) :
    ∃ map, Ordered Op map left right :=
  let result := (infer keys left right).get accepted
  ⟨result.1, result.2.down⟩

/-- Supply a numbered-family resolver obligation by running inference on
the two actual resolved bodies. -/
theorem inferResolved_sound {fn : Function V S} {left right : Closure Op m.Val fn}
    (accepted : (inferResolved keys left right).isSome = true) : Resolved m fn left right :=
  ((inferResolved keys left right).get accepted).down

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered
