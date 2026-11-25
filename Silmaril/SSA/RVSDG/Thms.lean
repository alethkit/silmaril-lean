module

public import Silmaril.SSA.RVSDG.Defs
import Silmaril.Proofs.SSA.RVSDG.Correspondence

/-! Exact correspondence for a fixed recursive numbering of the vertices. -/

public section

namespace Silmaril.SSA.RVSDG

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

/-- Collecting a term and reading its table in order recovers the term. -/
theorem Term.toTerm_toGraph (term : Term Op args past sigs outs) : term.toGraph.toTerm = term :=
  Proofs.toTerm_toGraph term

/-- Linearizing a graph and collecting the bindings recovers the numbered graph, including its
child tables and every input and result wire. -/
theorem Graph.toGraph_toTerm (graph : Graph Op args past sigs outs) : graph.toTerm.toGraph = graph :=
  Proofs.toGraph_toTerm graph

/-- Every vertex dependency in a whole region comes from a strictly earlier vertex. -/
theorem Graph.producer_lt (graph : Graph Op args [] sigs outs) (i : Fin sigs.length)
    {t : PortType V S} (p : Port (graph.nodes i).ins t) {j : Nat}
    (h : ((graph.nodes i).inputs.get p).producer = some j) : j < i.val :=
  Proofs.producer_lt graph i p h

/-- The graph evaluator and its linearization return the same typed results in every model. -/
theorem Graph.run_toTerm (graph : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (entry : Tuple m.Val args) : graph.toTerm.run m entry = graph.run m entry :=
  Proofs.eval_toTerm graph m entry PUnit.unit

/-- Building a numbered graph preserves the term's operational results. -/
theorem Term.run_toGraph (term : Term Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (entry : Tuple m.Val args) : term.toGraph.run m entry = term.run m entry := by
  rw [← Graph.run_toTerm, Term.toTerm_toGraph]

end Silmaril.SSA.RVSDG
