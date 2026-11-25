module

public import Silmaril.SSA.RVSDG.Defs
public import Mathlib.Logic.Relation

/-!
# Coloured firing semantics for the acyclic RVSDG fragment

Argument and output places carry typed colours. Reads retain the tokens, so one
published output can supply multiple users. A vertex has one control token: pending,
waiting on the selected child marking, or done with its output places marked.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Petri

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args head ins outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

abbrev Tokens {Ty : Type u} (F : Ty → Type w) (sigs : List (Ports Ty)) :=
  Locals (fun t => Option (F t)) sigs

/-- All colours at a signature are absent. -/
def absent {Ty : Type u} {F : Ty → Type w} : (ts : Ports Ty) → Tuple (fun t => Option (F t)) ts
  | [] => .nil
  | _ :: ts => .cons none (absent ts)

/-- Collect a tuple only when the token at every requested port is present. -/
def collect {Ty : Type u} {F : Ty → Type w} {ts : Ports Ty} :
    Tuple (fun t => Option (F t)) ts → Option (Tuple F ts)
  | .nil => some .nil
  | .cons x xs =>
    match x, collect xs with
    | some value, some rest => some (.cons value rest)
    | _, _ => none

/-- Read a colour from its argument or output place without removing the token. -/
def colour {Ty : Type u} {F : Ty → Type w} {args : Ports Ty} {past : List (Ports Ty)}
    (entry : Tuple F args) (tokens : Tokens F past) {t : Ty} : Origin args past t → Option (F t)
  | .arg port => some (entry.get port)
  | .output vertex port => (tokens.get vertex).get port

def read {Ty : Type u} {F : Ty → Type w} {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) (entry : Tuple F args) (tokens : Tokens F past) :
    Option (Tuple F users) :=
  collect (wires.map fun _ => colour entry tokens)

/-- A waiting token locks the chosen arm and carries its live marking. -/
inductive Vertex (Output : Type u) {count : Nat} (Child : Fin count → Type v) where
  | pending
  | waiting (arm : Fin count) (child : Child arm)
  | done (output : Output)

def Vertex.outputs {Ty : Type u} {F : Ty → Type w} {ts : Ports Ty}
    {count : Nat} {Child : Fin count → Type v} :
    Vertex (Tuple F ts) Child → Tuple (fun t => Option (F t)) ts
  | .done output => output.map fun _ => some
  | .pending | .waiting _ _ => absent ts

/-- The numbered node spine indexes a product of places. Its order is used to
resolve wire addresses. A later vertex may fire while an earlier one is pending. -/
def Marking (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term Op args past sigs outs → Type (max u w)
  | _, _, _, _, .ret _ => PUnit
  | _, _, _, _, .bind (head := head) node children rest =>
    Vertex (Tuple m.Val head) (fun j => Tuple m.Val node.shape.entry × Marking m (children j)) ×
      Marking m rest

/-- A fresh region has one pending token per vertex and no active children. -/
def pending (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (term : Term Op args past sigs outs) → Marking m term
  | _, _, _, _, .ret _ => PUnit.unit
  | _, _, _, _, .bind _ _ rest => (.pending, pending m rest)

/-- Completion needs every local vertex's done token and all result colours. -/
def finished (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (term : Term Op args past sigs outs) → Tuple m.Val args → Tokens m.Val past →
    Marking m term → Option (Tuple m.Val outs)
  | _, _, _, _, .ret results, entry, tokens, _ => read results entry tokens
  | _, _, _, _, .bind _ _ rest, entry, tokens, marking =>
    match marking.1 with
    | .done output => finished m rest entry (tokens.snoc (output.map fun _ => some)) marking.2
    | .pending | .waiting _ _ => none

/-- The transition attached to a primitive opcode. -/
def primitive (m : Model.{u, v, w} Op) (shape : Shape Op ins outs)
    (input : Tuple m.Val ins) : Option (Tuple m.Val outs) :=
  match shape with
  | .simple opcode => some (m.run opcode input)
  | .gamma _ => none

/-- The guard of a γ reads its selector and sends the remaining inputs to the selected arm. -/
def select (m : Model.{u, v, w} Op) (shape : Shape Op ins outs) (input : Tuple m.Val ins) :
    Option (Fin shape.regionCount × Tuple m.Val shape.entry) :=
  match shape with
  | .simple _ => none
  | .gamma _ => match input with
    | .cons choice entry => some (choice.down, entry)

/-- A completed child publishes its results at the structural node's output ports. -/
def publish (m : Model.{u, v, w} Op) (shape : Shape Op ins outs) :
    Fin shape.regionCount → Tuple m.Val shape.exit → Tuple m.Val outs :=
  match shape with
  | .simple _ => fun arm _ => arm.elim0
  | .gamma _ => fun _ output => output

/-- A single hierarchical firing. The input and prefix places are read-only here.
`later` exposes only the output places the preceding vertex has actually marked.
`advance` fires inside the live child carried by a waiting token. -/
inductive Fire (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (term : Term Op args past sigs outs) → Tuple m.Val args → Tokens m.Val past →
    Marking m term → Marking m term → Prop where
  | primitive
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {tail : Marking m rest}
      {input : Tuple m.Val node.ins} {output : Tuple m.Val head}
      (ready : read node.inputs entry tokens = some input)
      (result : Petri.primitive m node.shape input = some output) :
      Fire m (.bind node children rest) entry tokens (.pending, tail) (.done output, tail)
  | enter
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {tail : Marking m rest}
      {input : Tuple m.Val node.ins} {arm : Fin node.shape.regionCount}
      {received : Tuple m.Val node.shape.entry}
      (ready : read node.inputs entry tokens = some input)
      (guard : select m node.shape input = some (arm, received)) :
      Fire m (.bind node children rest) entry tokens (.pending, tail)
        (.waiting arm (received, pending m (children arm)), tail)
  | advance
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {tail : Marking m rest}
      {arm : Fin node.shape.regionCount} {received : Tuple m.Val node.shape.entry}
      {before after : Marking m (children arm)}
      (step : Fire m (past := []) (children arm) received PUnit.unit before after) :
      Fire m (.bind node children rest) entry tokens (.waiting arm (received, before), tail)
        (.waiting arm (received, after), tail)
  | commit
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {tail : Marking m rest}
      {arm : Fin node.shape.regionCount} {received : Tuple m.Val node.shape.entry}
      {child : Marking m (children arm)} {output : Tuple m.Val node.shape.exit}
      (ready : finished m (past := []) (children arm) received PUnit.unit child = some output) :
      Fire m (.bind node children rest) entry tokens (.waiting arm (received, child), tail)
        (.done (publish m node.shape arm output), tail)
  | later
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past}
      {vertex : Vertex (Tuple m.Val head)
        (fun j => Tuple m.Val node.shape.entry × Marking m (children j))}
      {before after : Marking m rest}
      (step : Fire m rest entry (tokens.snoc vertex.outputs) before after) :
      Fire m (.bind node children rest) entry tokens (vertex, before) (vertex, after)

abbrev GraphMarking (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs) :=
  Marking m graph.toTerm

/-- Install the graph's pending control tokens. Each execution supplies its fixed
root argument tokens through the `input` parameter of `Step`. -/
def initial (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs) : GraphMarking m graph :=
  pending m graph.toTerm

abbrev Step (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs) (input : Tuple m.Val args) :=
  Fire m (past := []) graph.toTerm input PUnit.unit

def result (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs) (input : Tuple m.Val args)
    (marking : GraphMarking m graph) : Option (Tuple m.Val outs) :=
  finished m (past := []) graph.toTerm input PUnit.unit marking

/-- A finite sequence of firings reaches a completed marking with the given result. -/
def Finishes (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) : Prop :=
  ∃ marking, Relation.ReflTransGen (Step m graph input) (initial m graph) marking ∧
    result m graph input marking = some output

end Silmaril.SSA.RVSDG.Petri
