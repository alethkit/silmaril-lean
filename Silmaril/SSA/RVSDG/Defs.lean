module

/-!
# A typed, acyclic RVSDG fragment

Primitive operations and multi-way γ nodes can appear in any region. A region's arguments
and results are ordered port tuples. Every input and result names one same-region origin.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG

universe u v w

/-- Dialects choose the value and state sorts. A control value selects one of its alternatives. -/
inductive PortType (ValueSort StateSort : Type u) where
  | value (sort : ValueSort)
  | state (sort : StateSort)
  | control (alternatives : Nat)

abbrev Ports (Ty : Type u) := List Ty

/-- An ordered tuple with one component of the indicated type at each port. -/
inductive Tuple {Ty : Type u} (F : Ty → Type v) : Ports Ty → Type (max u v) where
  | nil : Tuple F []
  | cons {t : Ty} {ts : Ports Ty} (head : F t) (tail : Tuple F ts) : Tuple F (t :: ts)

/-- A typed position in an ordered list of ports. -/
inductive Port {Ty : Type u} : Ports Ty → Ty → Type u where
  | head {t : Ty} {ts : Ports Ty} : Port (t :: ts) t
  | tail {t s : Ty} {ts : Ports Ty} (port : Port ts t) : Port (s :: ts) t

def Tuple.get {Ty : Type u} {F : Ty → Type v} {ts : Ports Ty} {t : Ty}
    (xs : Tuple F ts) (p : Port ts t) : F t :=
  match p, xs with
  | .head, .cons x _ => x
  | .tail p, .cons _ xs => xs.get p

def Tuple.map {Ty : Type u} {F : Ty → Type v} {G : Ty → Type w}
    (f : ∀ t, F t → G t) {ts : Ports Ty} : Tuple F ts → Tuple G ts
  | .nil => .nil
  | .cons x xs => .cons (f _ x) (xs.map f)

/-- A region argument or a port of an earlier node. Node numbers are local to a region. -/
inductive Origin {Ty : Type u} (args : Ports Ty) (past : List (Ports Ty)) (t : Ty) where
  | arg (port : Port args t)
  | output (node : Fin past.length) (port : Port past[node] t)

abbrev Wires {Ty : Type u} (args : Ports Ty) (past : List (Ports Ty)) (users : Ports Ty) :=
  Tuple (Origin args past) users

variable {V S : Type u}

abbrev Dialect (V S : Type u) := Ports (PortType V S) → Ports (PortType V S) → Type v

/-- A node's input and output signatures, before wiring and attaching nested regions. -/
inductive Shape (Op : Dialect.{u, v} V S) : Ports (PortType V S) → Ports (PortType V S) →
    Type (max u v) where
  | simple {ins outs : Ports (PortType V S)} (opcode : Op ins outs) : Shape Op ins outs
  | gamma {entry exit : Ports (PortType V S)} (extra : Nat) : Shape Op (.control (extra + 2) :: entry) exit

variable {Op : Dialect.{u, v} V S}

def Shape.regionCount {ins outs : Ports (PortType V S)} : Shape Op ins outs → Nat
  | .simple _ => 0
  | .gamma extra => extra + 2

def Shape.entry {ins outs : Ports (PortType V S)} : Shape Op ins outs → Ports (PortType V S)
  | .simple _ => []
  | @Shape.gamma _ _ _ entry _ _ => entry

def Shape.exit {ins outs : Ports (PortType V S)} : Shape Op ins outs → Ports (PortType V S)
  | .simple _ => []
  | @Shape.gamma _ _ _ _ exit _ => exit

/-- Header data for a node. Each subregion has its own list of node output signatures. -/
structure Node (Op : Dialect.{u, v} V S) (args : Ports (PortType V S))
    (past : List (Ports (PortType V S))) (outs : Ports (PortType V S)) where
  ins : Ports (PortType V S)
  shape : Shape Op ins outs
  inputs : Wires args past ins
  childSigs : Fin shape.regionCount → List (Ports (PortType V S))

/-- Extend the sequence of in-scope node signatures in binding order. -/
def extend {Ty : Type u} (past : List (Ports Ty)) : List (Ports Ty) → List (Ports Ty)
  | [] => past
  | head :: tail => extend (past ++ [head]) tail

/-- The in-scope signatures and the output signature at a numbered graph vertex. -/
def site {Ty : Type u} (past : List (Ports Ty)) :
    (sigs : List (Ports Ty)) → Fin sigs.length → List (Ports Ty) × Ports Ty
  | [], i => i.elim0
  | head :: tail, i => Fin.cases (past, head) (site (past ++ [head]) tail) i

abbrev Nodes (Op : Dialect.{u, v} V S) (args : Ports (PortType V S))
    (past sigs : List (Ports (PortType V S))) :=
  (i : Fin sigs.length) → Node Op args (site past sigs i).1 (site past sigs i).2

abbrev Children
    (Region : Ports (PortType V S) → List (Ports (PortType V S)) → List (Ports (PortType V S)) →
      Ports (PortType V S) → Type w)
    {args : Ports (PortType V S)} {past : List (Ports (PortType V S))}
    {outs : Ports (PortType V S)} (node : Node Op args past outs) :=
  (j : Fin node.shape.regionCount) →
    Region node.shape.entry [] (node.childSigs j) node.shape.exit

/-- Inductive region syntax. A let binds a tuple, and each γ arm starts with fresh local scope. -/
inductive Term (Op : Dialect.{u, v} V S) : (args : Ports (PortType V S)) →
    (past sigs : List (Ports (PortType V S))) → (outs : Ports (PortType V S)) →
      Type (max u v) where
  | ret {args outs : Ports (PortType V S)} {past : List (Ports (PortType V S))}
      (results : Wires args past outs) : Term Op args past [] outs
  | bind {args head outs : Ports (PortType V S)} {past tail : List (Ports (PortType V S))}
      (node : Node Op args past head)
      (children : (j : Fin node.shape.regionCount) →
        Term Op node.shape.entry [] (node.childSigs j) node.shape.exit)
      (rest : Term Op args (past ++ [head]) tail outs) : Term Op args past (head :: tail) outs

/-- A hierarchical graph given by vertex, child-region and result tables. A vertex may
read only arguments or outputs of lower-numbered vertices. The prefix parameter lets
algorithms operate on a suffix of a table. A whole region uses the empty prefix. -/
inductive Graph (Op : Dialect.{u, v} V S) : (args : Ports (PortType V S)) →
    (past sigs : List (Ports (PortType V S))) → (outs : Ports (PortType V S)) →
      Type (max u v) where
  | region {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      (nodes : Nodes Op args past sigs)
      (children : (i : Fin sigs.length) → (j : Fin (nodes i).shape.regionCount) →
        Graph Op (nodes i).shape.entry [] ((nodes i).childSigs j) (nodes i).shape.exit)
      (results : Wires args (extend past sigs) outs) : Graph Op args past sigs outs

variable {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

def Graph.nodes : Graph Op args past sigs outs → Nodes Op args past sigs
  | .region nodes _ _ => nodes

def Graph.children (g : Graph Op args past sigs outs) (i : Fin sigs.length) :
    Children (Graph Op) (g.nodes i) :=
  match g with
  | .region _ children _ => children i

def Graph.results : Graph Op args past sigs outs → Wires args (extend past sigs) outs
  | .region _ _ results => results

/-- A wire sourced from an argument has no producer vertex. -/
def Origin.producer {Ty : Type u} {args : Ports Ty} {past : List (Ports Ty)} {t : Ty} :
    Origin args past t → Option Nat
  | .arg _ => none
  | .output node _ => some node.val

/-- Prepend a vertex while retaining the absolute addresses used by the suffix. -/
def Nodes.cons (node : Node Op args past head) (nodes : Nodes Op args (past ++ [head]) sigs) :
    Nodes Op args past (head :: sigs) :=
  Fin.cases (motive := fun i => Node Op args (site past (head :: sigs) i).1
    (site past (head :: sigs) i).2) node nodes

/-- Only the prefix of available signatures changes when extending a vertex table. -/
def Graph.prepend (node : Node Op args past head) (children : Children (Graph Op) node) :
    Graph Op args (past ++ [head]) sigs outs → Graph Op args past (head :: sigs) outs
  | .region nodes subregions results =>
    let allNodes := Nodes.cons node nodes
    .region allNodes
      (Fin.cases (motive := fun i => Children (Graph Op) (allNodes i)) children subregions)
      results

/-- Collect the let sequence into a local vertex table, recursively assembling subregions. -/
def Term.toGraph : {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term Op args past sigs outs → Graph Op args past sigs outs
  | _, _, _, _, .ret results => .region (fun i => i.elim0) (fun i => i.elim0) results
  | _, _, _, _, .bind node children rest => rest.toGraph.prepend node (fun j => (children j).toGraph)

/-- Linearize one region's table in vertex-number order after linearizing its subregions. -/
def Term.fromTable {args outs : Ports (PortType V S)}
    (past : List (Ports (PortType V S))) :
    (sigs : List (Ports (PortType V S))) → (nodes : Nodes Op args past sigs) →
    ((i : Fin sigs.length) → Children (Term Op) (nodes i)) →
    Wires args (extend past sigs) outs → Term Op args past sigs outs
  | [], _, _, results => .ret results
  | head :: tail, nodes, children, results =>
    .bind (nodes 0) (children 0)
      (fromTable (past ++ [head]) tail (fun i => nodes i.succ) (fun i => children i.succ) results)

/-- Read the table in vertex-number order, independently within each region. -/
def Graph.toTerm : {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Graph Op args past sigs outs → Term Op args past sigs outs
  | _, _, _, _, .region nodes children results =>
    Term.fromTable _ _ nodes (fun i j => (children i j).toTerm) results

/-- Interpretation of port types. Control ports always carry an in-range branch number. -/
def PortType.Val (value : V → Type w) (state : S → Type w) : PortType V S → Type w
  | .value t => value t
  | .state t => state t
  | .control n => ULift (Fin n)

/-- A total deterministic interpretation. Effectful operations take and return state as data. -/
structure Model (Op : Dialect.{u, v} V S) where
  value : V → Type w
  state : S → Type w
  run {ins outs : Ports (PortType V S)} :
    Op ins outs → Tuple (PortType.Val value state) ins → Tuple (PortType.Val value state) outs

abbrev Model.Val (m : Model.{u, v, w} Op) := PortType.Val m.value m.state

/-- Runtime output tuples, stored in ascending vertex-number order. -/
def Locals {Ty : Type u} (F : Ty → Type w) : List (Ports Ty) → Type (max u w)
  | [] => PUnit
  | head :: tail => Tuple F head × Locals F tail

def Locals.get {Ty : Type u} {F : Ty → Type w} {past : List (Ports Ty)} (xs : Locals F past)
    (i : Fin past.length) : Tuple F past[i] :=
  match past with
  | [] => i.elim0
  | _ :: _ => Fin.cases (motive := fun j => Tuple F _[j]) xs.1 (fun j => xs.2.get j) i

def Locals.snoc {Ty : Type u} {F : Ty → Type w} {past : List (Ports Ty)} {head : Ports Ty}
    (xs : Locals F past) (x : Tuple F head) : Locals F (past ++ [head]) :=
  match past with
  | [] => (x, PUnit.unit)
  | _ :: _ => (xs.1, xs.2.snoc x)

/-- Resolve each edge at its origin. Multiple users can read the same origin. -/
def Wires.read {Ty : Type u} {F : Ty → Type w} {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) (entry : Tuple F args) (locals : Locals F past) :
    Tuple F users :=
  Tuple.map (fun _ wire => match wire with
    | .arg p => entry.get p
    | .output i p => (locals.get i).get p) wires

/-- Execute a primitive or evaluate just the selected child of a γ. -/
def Shape.eval (m : Model.{u, v, w} Op) {ins outs : Ports (PortType V S)} (shape : Shape Op ins outs)
    (runChild : Fin shape.regionCount → Tuple m.Val shape.entry → Tuple m.Val shape.exit)
    (inputs : Tuple m.Val ins) : Tuple m.Val outs :=
  match shape with
  | .simple opcode => m.run opcode inputs
  | .gamma _ => match inputs with
    | .cons choice entry => runChild choice.down entry

/-- Execute an inductive region. The environment extension binds a primitive or γ result tuple. -/
def Term.eval (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Tuple m.Val args → Locals m.Val past → Term Op args past sigs outs → Tuple m.Val outs
  | _, _, _, _, entry, locals, .ret results => results.read entry locals
  | _, _, _, _, entry, locals, .bind node children rest =>
    let result := node.shape.eval m
      (fun j input => (children j).eval m (past := []) input PUnit.unit) (node.inputs.read entry locals)
    rest.eval m entry (locals.snoc result)

/-- Fire once at each vertex in table order, then read the region's result wires. -/
def evalTable (m : Model.{u, v, w} Op) (entry : Tuple m.Val args) :
    (past sigs : List (Ports (PortType V S))) → Locals m.Val past →
    (nodes : Nodes Op args past sigs) →
    ((i : Fin sigs.length) → Fin (nodes i).shape.regionCount →
      Tuple m.Val (nodes i).shape.entry → Tuple m.Val (nodes i).shape.exit) →
    Wires args (extend past sigs) outs → Tuple m.Val outs
  | _, [], locals, _, _, results => results.read entry locals
  | past, head :: tail, locals, nodes, runChild, results =>
    let node := nodes 0
    let result := node.shape.eval m (runChild 0) (node.inputs.read entry locals)
    evalTable m entry (past ++ [head]) tail (locals.snoc result)
      (fun i => nodes i.succ) (fun i => runChild i.succ) results

/-- Execute the numbered graph directly, entering γ children with a fresh local store. -/
def Graph.eval (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Tuple m.Val args → Locals m.Val past → Graph Op args past sigs outs → Tuple m.Val outs
  | _, _, _, _, entry, locals, .region nodes children results =>
    evalTable m entry _ _ locals nodes (fun i j input => (children i j).eval m (past := []) input PUnit.unit)
      results

/-- Evaluate a whole term region from its arguments. -/
def Term.run (term : Term Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (entry : Tuple m.Val args) : Tuple m.Val outs :=
  term.eval m (past := []) entry PUnit.unit

/-- Evaluate a whole graph region from its arguments. -/
def Graph.run (graph : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (entry : Tuple m.Val args) : Tuple m.Val outs :=
  graph.eval m (past := []) entry PUnit.unit

end Silmaril.SSA.RVSDG
