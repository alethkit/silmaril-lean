module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Check.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Proofs

open Local (Renaming)
open NestedTheta.Equality (OpcodeCode)

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S} [DecidableEq (Ty V S)]
variable {args outs : Ports (Ty V S)} {pastL pastR : List (Ports (Ty V S))}

theorem check_results_iff (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] (mapping : Renaming)
    (left : Wires args pastL outs) (right : Wires args pastR outs) :
    (check keys mapping (resultsOnly (Op := Op) left) (resultsOnly right)).isSome = true ↔
      left.addresses.map (Address.rename mapping.vertices) = right.addresses := by
  by_cases edges : left.addresses.map (Address.rename mapping.vertices) = right.addresses
  · simp [check, termSize, scan, NestedTheta.Graph.toTerm, NestedTheta.Term.fromTable, edges]
  · simp [check, termSize, scan, NestedTheta.Graph.toTerm, NestedTheta.Term.fromTable, edges]

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Proofs
