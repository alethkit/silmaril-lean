module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs

/-! A chosen typed graph renumbering and its action on live markings. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

/-- The data in a typed graph isomorphism, retained so one trace uses the
same vertex and child maps even when a graph has automorphisms. -/
inductive Renumbering (Op : Dialect.{u, v} V S) :
    {argsL argsR outsL outsR : Ports (PortType V S)} →
    {sigsL sigsR : List (Ports (PortType V S))} →
    Graph Op argsL [] sigsL outsL → Graph Op argsR [] sigsR outsR → Type (max u v) where
  | intro {argsL argsR outsL outsR : Ports (PortType V S)}
      {sigsL sigsR : List (Ports (PortType V S))}
      {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
      (entry : argsL = argsR) (exit : outsL = outsR)
      (ids : Fin sigsL.length ≃ Fin sigsR.length)
      (labels : ∀ i, (left.nodes i).label = (right.nodes (ids i)).label)
      (inputs : ∀ i, (left.nodes i).inputs.addresses.map (Address.rename (renameVertex ids)) =
        (right.nodes (ids i)).inputs.addresses)
      (results : left.results.addresses.map (Address.rename (renameVertex ids)) =
        right.results.addresses)
      (children : ∀ i (arm : Fin (left.nodes i).kind.arity),
        Renumbering Op (left.children i arm)
          (right.children (ids i) (Fin.cast (congrArg NodeLabel.arity (labels i)) arm))) :
      Renumbering Op left right

abbrev Local (m : Model.{u, v, w} Op) (label : NodeLabel Op) (C : Fin label.arity → Type (max u w)) :=
  RVSDG.Petri.Vertex (Tuple m.Val label.outs) (fun arm => Tuple m.Val label.kind.entry × C arm)

abbrev LocalMarking (m : Model.{u, v, w} Op) (node : Node Op args past outs)
    (children : Children (Term Op) node) :=
  Local m node.label (fun arm => Marking m (children arm))

/-- Look up a local marking in the spine decoded from a vertex table. -/
def markingAt (m : Model.{u, v, w} Op) {args outs : Ports (PortType V S)} :
    (past sigs : List (Ports (PortType V S))) → (nodes : Nodes Op args past sigs) →
    (children : (i : Fin sigs.length) → Children (Term Op) (nodes i)) →
    (wires : Wires args (extend past sigs) outs) →
    Marking m (Term.fromTable past sigs nodes children wires) →
    (i : Fin sigs.length) → LocalMarking m (nodes i) (children i)
  | _, [], _, _, _, _, i => i.elim0
  | past, head :: tail, nodes, children, wires, marks, i =>
    Fin.cases (motive := fun j => LocalMarking m (nodes j) (children j))
      marks.1 (markingAt m (past ++ [head]) tail (fun j => nodes j.succ)
        (fun j => children j.succ) wires marks.2) i

/-- The phase and saved data at one vertex, including the live marking of its selected child. -/
def graphMarkingAt (m : Model.{u, v, w} Op) (g : Graph Op args [] sigs outs)
    (marking : GraphMarking m g) (i : Fin sigs.length) :
    LocalMarking m (g.nodes i) (fun j => (g.children i j).toTerm) :=
  match g with
  | .region nodes children results =>
    markingAt m [] sigs nodes (fun i j => (children i j).toTerm) results marking i

/-- Both vertex phases must agree. A waiting pair has equal saved inputs
and recursively matching markings under the map of the chosen child. -/
def Local.Matches (m : Model.{u, v, w} Op) {left right : NodeLabel Op}
    (same : left = right) {C : Fin left.arity → Type (max u w)}
    {D : Fin right.arity → Type (max u w)}
    (children : ∀ arm, C arm → D (Fin.cast (congrArg NodeLabel.arity same) arm) → Prop)
    (src : Local m left C) (dst : Local m right D) : Prop := by
  subst right
  exact match src, dst with
  | .pending, .pending => True
  | .done x, .done y => x = y
  | .waiting j (x, sub), .waiting k (y, sub') =>
    ∃ eq : j = k, x = y ∧ children j sub (eq.symm ▸ sub')
  | _, _ => False

/-- Compare every marked vertex at its image under the chosen renumbering. -/
def Renumbering.Matches (m : Model.{u, v, w} Op) :
    {argsL argsR outsL outsR : Ports (PortType V S)} → {sigsL sigsR : List (Ports (PortType V S))} →
    {left : Graph Op argsL [] sigsL outsL} → {right : Graph Op argsR [] sigsR outsR} →
    Renumbering Op left right → GraphMarking m left → GraphMarking m right → Prop
  | _, _, _, _, _, _, left, right, .intro _ _ ids labels _ _ children, before, after =>
    ∀ i, Local.Matches m (labels i) (fun j => Matches m (children i j))
      (graphMarkingAt m left before i) (graphMarkingAt m right after (ids i))

/-- Count fine-grained steps, including entry, commit and restart. -/
inductive Steps {State : Type w} (step : State → State → Prop) : Nat → State → State → Prop where
  | refl (state : State) : Steps step 0 state state
  | tail {n : Nat} {a b c : State} (earlier : Steps step n a b) (last : step b c) :
      Steps step (n + 1) a c

/-- Two sequences take one firing each at every position and their markings
match at the initial point and after each firing. -/
inductive PairedSteps {L : Type u} {R : Type v} (stepL : L → L → Prop) (stepR : R → R → Prop)
    (relatedMarks : L → R → Prop) : Nat → L → R → L → R → Prop where
  | refl {a : L} {b : R} (related : relatedMarks a b) : PairedSteps stepL stepR relatedMarks 0 a b a b
  | tail {n : Nat} {a a' a'' : L} {b b' b'' : R}
      (earlier : PairedSteps stepL stepR relatedMarks n a b a' b')
      (left : stepL a' a'') (right : stepR b' b'') (related : relatedMarks a'' b'') :
      PairedSteps stepL stepR relatedMarks (n + 1) a b a'' b''

end Silmaril.SSA.RVSDG.NestedTheta.Petri
