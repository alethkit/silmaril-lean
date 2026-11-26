module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs

/-! # Ordering certificate for a coloured memory activation -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open RVSDG (Dialect Origin Wires)
open RVSDG.OrderedRuntime.Structured (Threaded Ty nextRuntime runtime runtimePort)
open RVSDG.NestedTheta.Petri (Marking pending)

variable {args : List ValueSort}

/-- The acyclic body of the actual numbered θ, embedded in the same
hierarchical syntax used by the firing model. -/
def Graph.activation (graph : Graph args) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier args) [] graph.thetaSigs
      (RVSDG.Theta.BodyResults (carrier args)) :=
  (RVSDG.NestedTheta.Term.ofBase graph.thetaBody).toGraph

namespace Firing

variable {Op : Dialect ValueSort PUnit}
variable {entry outs : List (Ty ValueSort)} {past sigs : List (List (Ty ValueSort))}

/-- At each primitive the state input is the designated heap wire. The
successor uses that primitive's final port as its designated wire. -/
inductive HeapChain (Op : Dialect ValueSort PUnit) (entry outs : List (Ty ValueSort)) :
    {past sigs : List (List (Ty ValueSort))} → Origin entry past runtime →
      RVSDG.Term Op entry past sigs outs → Prop where
  | ret {past : List (List (Ty ValueSort))} {live : Origin entry past runtime}
      (results : Wires entry past outs) : HeapChain Op entry outs live (.ret results)
  | bind {past sigs : List (List (Ty ValueSort))} {ins out : List (Ty ValueSort)}
      {live : Origin entry past runtime} (op : Op (Threaded ins) (Threaded out))
      (wires : Wires entry past (Threaded ins)) (heap : wires.get (runtimePort ins) = live)
      {rest : RVSDG.Term Op entry (past ++ [Threaded out]) sigs outs}
      (tail : HeapChain Op entry outs (nextRuntime past out) rest) :
      HeapChain Op entry outs live
        (.bind ⟨_, .simple op, wires, fun i => i.elim0⟩ (fun i => i.elim0) rest)

/-- The existing marking has exactly this many done vertices in order,
followed by pending vertices. Child markings are absent in this predicate. -/
def DonePrefix (model : RVSDG.Model Op) :
    {entry outs : List (Ty ValueSort)} → {past sigs : List (List (Ty ValueSort))} →
    (term : RVSDG.NestedTheta.Term Op entry past sigs outs) → Marking model term → Nat → Prop
  | _, _, _, _, .ret _, _, count => count = 0
  | _, _, _, _, .bind _ _ rest, marking, count =>
    match marking.1 with
    | .pending => count = 0 ∧ marking.2 = pending model rest
    | .waiting _ _ => False
    | .done _ => ∃ before, count = before + 1 ∧ DonePrefix model rest marking.2 before

end Firing

end Silmaril.SSA.SeaOfNodes.Memory.Loop
