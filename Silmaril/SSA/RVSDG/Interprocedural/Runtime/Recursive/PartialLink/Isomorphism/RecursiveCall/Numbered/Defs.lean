module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamily.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs

/-! An ordered, typed certificate on numbered region tables. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Local (Renaming)
open Continuation.Partial (Primitives)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {args outs : Ports (Ty V S)} {past : List (Ports (Ty V S))}

abbrev Graph (Op : Dialect.{u, v} (ValueSort V S) S) :=
  NestedTheta.Graph (Instruction Op)

abbrev resultsOnly (wires : Wires args past outs) : Graph Op args past [] outs :=
  .region (fun i => i.elim0) (fun i => i.elim0) wires

/-- The remaining rows retain their absolute addresses in the enlarged
prefix. The head's child regions still start in their own empty scopes. -/
def suffix {head : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
    (graph : Graph Op args past (head :: sigs) outs) : Graph Op args (past ++ [head]) sigs outs :=
  .region (fun i => graph.nodes i.succ) (fun i => graph.children i.succ) graph.results

/-- Check the rows of two numbered regions in execution order. A matched
row has one typed label, related ordered operand addresses, and checked
child tables at the original arm indices. Each child uses its own map.
An unmatched row must be an empty γ with empty child tables, so it can
neither run a primitive nor supply a result wire. -/
inductive Ordered (Op : Dialect.{u, v} (ValueSort V S) S) :
    (mapping : Renaming) → {args outs : Ports (Ty V S)} →
    {pastL pastR sigsL sigsR : List (Ports (Ty V S))} →
    Graph Op args pastL sigsL outs → Graph Op args pastR sigsR outs → Prop where
  | ret {mapping : Renaming} {args outs : Ports (Ty V S)} {pastL pastR : List (Ports (Ty V S))}
      (left : Wires args pastL outs) (right : Wires args pastR outs)
      (edges : left.addresses.map (Address.rename mapping.vertices) = right.addresses) :
    Ordered Op mapping (resultsOnly left) (resultsOnly right)
  | bind {mapping : Renaming} {args ins head outs : Ports (Ty V S)}
      {pastL pastR sigsL sigsR : List (Ports (Ty V S))}
      (kind : NestedTheta.Kind (Instruction Op) ins head)
      (left : Wires args pastL ins) (right : Wires args pastR ins)
      {csL csR : Fin kind.arity → List (Ports (Ty V S))}
      {childL : (i : Fin kind.arity) → Graph Op kind.entry [] (csL i) kind.exit}
      {childR : (i : Fin kind.arity) → Graph Op kind.entry [] (csR i) kind.exit}
      {restL : Graph Op args (pastL ++ [head]) sigsL outs}
      {restR : Graph Op args (pastR ++ [head]) sigsR outs}
      (position : mapping.vertices pastL.length = pastR.length)
      (edges : left.addresses.map (Address.rename mapping.vertices) = right.addresses)
      (children : ∀ i, Ordered Op (mapping.child pastL.length i.val) (childL i) (childR i))
      (rest : Ordered Op mapping restL restR) :
    Ordered Op mapping (restL.prepend ⟨ins, kind, left, csL⟩ childL)
      (restR.prepend ⟨ins, kind, right, csR⟩ childR)
  | emptyLeft {mapping : Renaming} {args entry outs : Ports (Ty V S)}
      {pastL pastR sigsL sigsR : List (Ports (Ty V S))} {extra : Nat}
      (wires : Wires args pastL (.control (extra + 2) :: entry))
      {restL : Graph Op args (pastL ++ [[]]) sigsL outs} {right : Graph Op args pastR sigsR outs}
      (rest : Ordered Op mapping restL right) :
    Ordered Op mapping (restL.prepend (emptyGamma wires) (fun _ => resultsOnly .nil)) right
  | emptyRight {mapping : Renaming} {args entry outs : Ports (Ty V S)}
      {pastL pastR sigsL sigsR : List (Ports (Ty V S))} {extra : Nat}
      (wires : Wires args pastR (.control (extra + 2) :: entry))
      {left : Graph Op args pastL sigsL outs} {restR : Graph Op args (pastR ++ [[]]) sigsR outs}
      (rest : Ordered Op mapping left restR) :
    Ordered Op mapping left (restR.prepend (emptyGamma wires) (fun _ => resultsOnly .nil))

/-- The numbered bodies of the two actual resolved callables must have
the same typed capture boundary. Member slot and capture provenance are
supplied independently by the linker's `ValueRelated` relation. -/
inductive Resolved (m : Machine.{u, v, w} Op) (fn : Function V S) :
    Closure Op m.Val fn → Closure Op m.Val fn → Prop where
  | intro {context : Ports (Ty V S)} {left right : Tuple m.Val context}
      {sigsL sigsR : List (Ports (Ty V S))} {mapping : Renaming}
      {bodyL : Graph Op (context ++ fn.args) [] sigsL fn.results}
      {bodyR : Graph Op (context ++ fn.args) [] sigsR fn.results}
      (graphs : Ordered Op mapping bodyL bodyR) :
    Resolved m fn ⟨context, left, sigsL, bodyL⟩ ⟨context, right, sigsR, bodyR⟩

/-- A client supplies closure under primitives and actual capture reads.
The paired obligation concerns only numbered graphs selected by the real
resolver, including fixed φ slots and ordinary λ closures. -/
structure CheckedFamily (primitives : Primitives m σ) (ids : GlobalRel) (left right : Family m) : Prop where
  closedL : Closed primitives left
  closedR : Closed primitives right
  graphs : ∀ {args outs : Ports (Ty V S)} {calleeL calleeR : m.Val (.value (.function args outs))},
    left calleeL → right calleeR → ValueRelated m ids calleeL calleeR →
    Resolved m ⟨args, outs⟩ (resolve m calleeL) (resolve m calleeR)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered
