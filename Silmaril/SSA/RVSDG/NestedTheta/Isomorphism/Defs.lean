module

public import Silmaril.SSA.RVSDG.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Defs

/-! Typed isomorphism for nested γ and θ regions. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} V S}

def Graph.nodes {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))} :
    Graph Op args past sigs outs → Nodes Op args past sigs
  | .region nodes _ _ => nodes

def Graph.children {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
    (graph : Graph Op args past sigs outs) (i : Fin sigs.length) :
    Children (Graph Op) (graph.nodes i) :=
  match graph with
  | .region _ children _ => children i

def Graph.results {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))} :
    Graph Op args past sigs outs → Wires args (extend past sigs) outs
  | .region _ _ results => results

/-- A vertex label includes its ordered signatures, node kind and primitive opcode. -/
structure NodeLabel (Op : Dialect.{u, v} V S) where
  ins : Ports (PortType V S)
  outs : Ports (PortType V S)
  kind : Kind Op ins outs

def NodeLabel.arity (label : NodeLabel Op) : Nat := label.kind.arity

def Node.label {args outs : Ports (PortType V S)} {past : List (Ports (PortType V S))}
    (node : Node Op args past outs) : NodeLabel Op :=
  ⟨node.ins, outs, node.kind⟩

/-- Hierarchical, typed port-graph isomorphism. Region arguments and results
are fixed by position and type. At each region there is a vertex bijection
preserving labels, all operand and result edges, and every child at its
original arm or body position. The bijections may change the topological numbering. -/
inductive Graph.Isomorphic {V S : Type u} (Op : Dialect.{u, v} V S) :
    {leftArgs rightArgs leftOut rightOut : Ports (PortType V S)} →
    {leftSigs rightSigs : List (Ports (PortType V S))} →
    Graph Op leftArgs [] leftSigs leftOut → Graph Op rightArgs [] rightSigs rightOut → Prop where
  | intro {leftArgs rightArgs leftOut rightOut : Ports (PortType V S)}
      {leftSigs rightSigs : List (Ports (PortType V S))}
      {left : Graph Op leftArgs [] leftSigs leftOut} {right : Graph Op rightArgs [] rightSigs rightOut}
      (entry : leftArgs = rightArgs) (exit : leftOut = rightOut)
      (ids : Fin leftSigs.length ≃ Fin rightSigs.length)
      (labels : ∀ i, (left.nodes i).label = (right.nodes (ids i)).label)
      (inputs : ∀ i, (left.nodes i).inputs.addresses.map (Address.rename (renameVertex ids)) =
        (right.nodes (ids i)).inputs.addresses)
      (results : left.results.addresses.map (Address.rename (renameVertex ids)) =
        right.results.addresses)
      (children : ∀ i (arm : Fin (left.nodes i).kind.arity),
        Graph.Isomorphic Op (left.children i arm)
          (right.children (ids i) (Fin.cast (congrArg NodeLabel.arity (labels i)) arm))) :
      Graph.Isomorphic Op left right

end Silmaril.SSA.RVSDG.NestedTheta
