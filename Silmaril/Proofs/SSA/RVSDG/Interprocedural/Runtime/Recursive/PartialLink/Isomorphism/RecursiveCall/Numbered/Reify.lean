module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Proofs

open Local (Renaming)

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args head outs : Ports (Ty V S)} {past pastL pastR sigs sigsL sigsR : List (Ports (Ty V S))}
variable {mapping : Renaming}

private theorem decode_prepend (node : NestedTheta.Node (Instruction Op) args past head)
    (children : NestedTheta.Children (Graph Op) node) (rest : Graph Op args (past ++ [head]) sigs outs) :
    (rest.prepend node children).toTerm = .bind node (fun i => (children i).toTerm) rest.toTerm := by
  cases rest
  rfl

private theorem results_prepend (node : NestedTheta.Node (Instruction Op) args past head)
    (children : NestedTheta.Children (Graph Op) node) (rest : Graph Op args (past ++ [head]) sigs outs) :
    (rest.prepend node children).results = rest.results := by
  cases rest
  rfl

theorem schedule {left : Graph Op args pastL sigsL outs} {right : Graph Op args pastR sigsR outs}
    (checked : Ordered Op mapping left right) :
    Schedule Op mapping.vertices left.toTerm right.toTerm := by
  induction checked with
  | ret left right edges => exact .ret left right edges
  | bind kind left right position edges _ _ children rest =>
    rw [decode_prepend, decode_prepend]
    cases kind with
    | theta =>
      exact .theta left right position edges (children (0 : Fin 1)) rest
    | base shape =>
      cases shape with
      | simple instruction => exact .bind instruction left right position edges rest
      | gamma => exact .gamma left right position edges children rest
  | emptyLeft wires _ rest =>
    rw [decode_prepend]
    exact .emptyLeft wires rest
  | emptyRight wires _ rest =>
    rw [decode_prepend]
    exact .emptyRight wires rest

theorem results_related {left : Graph Op args pastL sigsL outs} {right : Graph Op args pastR sigsR outs}
    (checked : Ordered Op mapping left right) :
    left.results.addresses.map (Address.rename mapping.vertices) = right.results.addresses := by
  induction checked with
  | ret left right edges => exact edges
  | bind _ _ _ _ _ _ _ _ rest =>
    rw [results_prepend, results_prepend]
    exact rest
  | emptyLeft _ _ rest => rw [results_prepend]; exact rest
  | emptyRight _ _ rest => rw [results_prepend]; exact rest

theorem prepend_head {head : Ports (Ty V S)} (graph : Graph Op args past (head :: sigs) outs) :
    NestedTheta.Graph.prepend (past := past) (head := head) (graph.nodes 0) (graph.children 0) (suffix graph) =
      graph := by
  let rebuilt : Graph Op args past (head :: sigs) outs :=
    NestedTheta.Graph.prepend (past := past) (head := head) (graph.nodes 0) (graph.children 0) (suffix graph)
  have same : rebuilt.toTerm = graph.toTerm := by cases graph; rfl
  exact (NestedTheta.Graph.toGraph_toTerm rebuilt).symm.trans
    ((congrArg NestedTheta.Term.toGraph same).trans (NestedTheta.Graph.toGraph_toTerm graph))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Proofs
