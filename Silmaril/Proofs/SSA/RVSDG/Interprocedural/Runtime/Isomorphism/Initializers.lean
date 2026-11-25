module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Table

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {args args' outs outs' : Ports (Ty V S)}
variable {past sigs sigs' : List (Ports (Ty V S))}

private def initializerRows (m : Machine.{u, v, w} Op) (nodes : RVSDG.Nodes Op args past sigs)
    (children : ∀ i, RVSDG.Children (RVSDG.Term Op) (nodes i)) : Rows m args past sigs :=
  fun i => ⟨(nodes i).ins, (nodes i).inputs, fun input => some
    (evalShape m (nodes i).shape
      (fun j args => evalInitializer m (past := []) (children i j) args PUnit.unit) input)⟩

private theorem initializer_fromTable (m : Machine.{u, v, w} Op) (nodes : RVSDG.Nodes Op args past sigs)
    (children : ∀ i, RVSDG.Children (RVSDG.Term Op) (nodes i))
    (wires : Wires args (extend past sigs) outs) (entry : Tuple m.Val args) (values : Locals m.Val past) :
    some (evalInitializer m (RVSDG.Term.fromTable past sigs nodes children wires) entry values) =
      runRows entry past sigs values (initializerRows m nodes children) wires := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    exact ih (fun i => nodes i.succ) (fun i j => children i.succ j) wires
      (values.snoc (evalShape m (nodes 0).shape
        (fun j input => evalInitializer m (past := []) (children 0 j) input PUnit.unit)
        ((nodes 0).inputs.read entry values)))

private theorem initializer_graph (m : Machine.{u, v, w} Op) (graph : RVSDG.Graph Op args [] sigs outs)
    (entry : Tuple m.Val args) :
    some (evalInitializer m (past := []) graph.toTerm entry PUnit.unit) =
      runRows entry [] sigs PUnit.unit
        (initializerRows m graph.nodes (fun i arm => (graph.children i arm).toTerm)) graph.results := by
  cases graph with
  | region nodes children wires =>
    exact initializer_fromTable m nodes (fun i j => (children i j).toTerm) wires entry PUnit.unit

private theorem shape_related (respects : PrimitivesRespect m ids) {left right : RVSDG.NodeLabel Op}
    (same : left = right)
    (runL : Fin left.arity → Tuple m.Val left.shape.entry → Tuple m.Val left.shape.exit)
    (runR : Fin right.arity → Tuple m.Val right.shape.entry → Tuple m.Val right.shape.exit)
    (inputL : Tuple m.Val left.ins) (inputR : Tuple m.Val right.ins)
    (paired : TupleRelated m ids inputL inputR)
    (subregions : ∀ arm inputL inputR, TupleRelated m ids inputL inputR →
      TupleRelated m ids (runL arm inputL) (runR (Fin.cast (congrArg RVSDG.NodeLabel.arity same) arm) inputR)) :
    TupleRelated m ids (evalShape m left.shape runL inputL) (evalShape m right.shape runR inputR) := by
  subst right
  obtain ⟨ins, outs, shape⟩ := left
  cases shape with
  | simple op => exact respects op paired
  | gamma extra =>
    cases paired with
    | cons tag payload =>
      cases tag with
      | control tag => exact subregions tag _ _ payload

theorem initializer_related (respects : PrimitivesRespect m ids)
    {left : RVSDG.Graph Op args [] sigs outs} {right : RVSDG.Graph Op args' [] sigs' outs'}
    (iso : RVSDG.Graph.Isomorphic Op left right)
    (inputL : Tuple m.Val args) (inputR : Tuple m.Val args') (entry : TupleRelated m ids inputL inputR) :
    TupleRelated m ids (evalInitializer m (past := []) left.toTerm inputL PUnit.unit)
      (evalInitializer m (past := []) right.toTerm inputR PUnit.unit) := by
  induction iso with
  | @intro args args' outs outs' sigs sigs' left right _ _ rename labels operands results _ children =>
    have paired : RunRelated m ids (some (evalInitializer m (past := []) left.toTerm inputL PUnit.unit))
        (some (evalInitializer m (past := []) right.toTerm inputR PUnit.unit)) := by
      rw [initializer_graph, initializer_graph]
      refine runRows_related rename inputL inputR entry _ _ _ _ operands results ?_
      intro i leftInput rightInput related
      exact .some (shape_related respects (labels i) _ _ leftInput rightInput related (children i))
    cases paired with
    | some related => exact related

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Proofs
