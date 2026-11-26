module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Check.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Check.Results

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Local (Renaming)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S} [DecidableEq (Ty V S)]
variable {m : Machine.{u, v, w} Op}
variable {args outs : Ports (Ty V S)} {pastL pastR sigsL sigsR : List (Ports (Ty V S))}
variable {keys : OpcodeCode (Instruction Op)} [DecidableEq keys.Key] {mapping : Renaming}

/-- An accepted table pair has an ordered certificate for the supplied
map and hence reifies to a runtime schedule. -/
theorem check_sound {left : Graph Op args pastL sigsL outs} {right : Graph Op args pastR sigsR outs}
    (accepted : (check keys mapping left right).isSome = true) : Ordered Op mapping left right :=
  ((check keys mapping left right).get accepted).down

/-- Use the executable checker in the numbered family's resolver field. -/
theorem checkResolved_sound {fn : Function V S} {left right : Closure Op m.Val fn}
    (accepted : (checkResolved keys mapping left right).isSome = true) : Resolved m fn left right :=
  ((checkResolved keys mapping left right).get accepted).down

/-- On result-only tables the check is complete for the supplied map.
In particular a mismatch here depends only on the ordered wire addresses. -/
theorem check_results_iff (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] (mapping : Renaming)
    (left : Wires args pastL outs) (right : Wires args pastR outs) :
    (check keys mapping (resultsOnly (Op := Op) left) (resultsOnly right)).isSome = true ↔
      left.addresses.map (Address.rename mapping.vertices) = right.addresses :=
  Proofs.check_results_iff keys mapping left right

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered
