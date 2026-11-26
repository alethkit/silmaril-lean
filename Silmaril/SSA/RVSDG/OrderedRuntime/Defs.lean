module

public import Silmaril.SSA.RVSDG.Defs
public import Silmaril.Semantics.RuntimeWires.Computations.Defs
public import Mathlib.CategoryTheory.Types.Basic

/-! # Ordered RVSDG chains with one runtime wire

Each step consumes the entire ordered result of its predecessor. The first
port is the unique runtime; the others are the polygraph's value word.
Pure generators carry the runtime through and effectful generators act on it.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime

open CategoryTheory
open Silmaril.RuntimeWires
open scoped MonoidalCategory

universe u v w d h
variable {G : EffectfulPolygraph.{u, v}}

abbrev Ty (G : EffectfulPolygraph.{u, v}) := PortType G.Obj PUnit.{u + 1}

/-- Order the runtime before the value ports, as in the runtime presentation. -/
def ports (G : EffectfulPolygraph.{u, v}) (word : List G.Obj) : Ports (Ty G) :=
  .state PUnit.unit :: word.map .value

inductive Instruction (G : EffectfulPolygraph.{u, v}) : List G.Obj → List G.Obj → Type (max u v)
  | pure (e : G.pure.Edge) : Instruction G (G.pure.source e) (G.pure.target e)
  | effect (e : G.effect.Edge) : Instruction G (G.effect.source e) (G.effect.target e)

inductive Opcode (G : EffectfulPolygraph.{u, v}) : Dialect G.Obj PUnit.{u + 1}
  | ordered {A B : List G.Obj} (f : Instruction G A B) : Opcode G (ports G A) (ports G B)

def lastIndex (head : Ports (Ty G)) :
    (past : List (Ports (Ty G))) → Fin (past ++ [head]).length
  | [] => ⟨0, Nat.zero_lt_succ _⟩
  | _ :: tail => (lastIndex head tail).succ

def lastPort {head : Ports (Ty G)} {t : Ty G} (p : Port head t) :
    (past : List (Ports (Ty G))) → Port (past ++ [head])[lastIndex head past] t
  | [] => p
  | _ :: tail => lastPort p tail

/-- The current value word and runtime are supplied by the arguments, or by
the last vertex of a nonempty prefix. -/
inductive Frontier (G : EffectfulPolygraph.{u, v}) (root : List G.Obj) :
    List (Ports (Ty G)) → List G.Obj → Type (max u v)
  | entry : Frontier G root [] root
  | vertex (past : List (Ports (Ty G))) (A : List G.Obj) : Frontier G root (past ++ [ports G A]) A

variable {root A B : List G.Obj} {past sigs : List (Ports (Ty G))}

def Frontier.origin {t : Ty G} (f : Frontier G root past A) (p : Port (ports G A) t) :
    Origin (ports G root) past t :=
  match f with
  | .entry => .arg p
  | .vertex past A => .output (lastIndex (ports G A) past) (lastPort p past)

def route {args : Ports (Ty G)} {past : List (Ports (Ty G))} :
    (ts : Ports (Ty G)) → (∀ {t : Ty G}, Port ts t → Origin args past t) → Wires args past ts
  | [], _ => .nil
  | _ :: tail, source => .cons (source .head) (route tail fun p => source (.tail p))

def node (f : Frontier G root past A) (op : Instruction G A B) :
    Node (Opcode G) (ports G root) past (ports G B) :=
  ⟨ports G A, .simple (.ordered op), route _ f.origin, fun j => j.elim0⟩

/-- Syntactic admission of an actual RVSDG binding sequence. Every input
and result uses the entire current frontier once and in order. -/
inductive Chain (G : EffectfulPolygraph.{u, v}) (root B : List G.Obj) :
    {past : List (Ports (Ty G))} → {A : List G.Obj} → Frontier G root past A →
    {sigs : List (Ports (Ty G))} → Term (Opcode G) (ports G root) past sigs (ports G B) →
    Type (max u v)
  | ret {past : List (Ports (Ty G))} (f : Frontier G root past B) :
      Chain G root B f (.ret (route _ f.origin))
  | bind {A next : List G.Obj} {past sigs : List (Ports (Ty G))}
      (f : Frontier G root past A) (op : Instruction G A next)
      {rest : Term (Opcode G) (ports G root) (past ++ [ports G next]) sigs (ports G B)} :
      Chain G root B (.vertex past next) rest →
      Chain G root B f (.bind (node f op) (fun j => j.elim0) rest)

/-- Interpret an admitted chain using only identities and ordered composition. -/
def Chain.fold {C : Type d} [Category.{h} C]
    (obj : List G.Obj → C)
    (one : ∀ {A B}, Instruction G A B → (obj A ⟶ obj B))
    : {past : List (Ports (Ty G))} → {A : List G.Obj} → {f : Frontier G root past A} →
      {sigs : List (Ports (Ty G))} → {t : Term (Opcode G) (ports G root) past sigs (ports G B)} →
      Chain G root B f t → (obj A ⟶ obj B)
  | _, _, _, _, _, .ret _ => 𝟙 _
  | _, _, _, _, _, .bind _ op rest => one op ≫ rest.fold obj one

open Silmaril.RuntimeWires.Presentation (Computations)

/-- Pure instructions tensor with the identity runtime; effects use a
generator whose boundary already consumes and returns the runtime. -/
def Instruction.diagram (op : Instruction G A B) :
    Diagram (Presentation.signature G)
      (none :: Presentation.values A) (none :: Presentation.values B) :=
  match op with
  | .pure e => .tensor (.id [none]) (Presentation.pureDiagram e)
  | .effect e => Diagram.gen (S := Presentation.signature G) (Presentation.Edge.effect e)

def Instruction.arrow (op : Instruction G A B) :
    (⟨A⟩ : Computations G) ⟶ (⟨B⟩ : Computations G) :=
  Diagram.Presented.ofTerm op.diagram

/-- Interpret the actual numbered graph, with an admitted linearization, in
the repository's single-runtime computation category. -/
def denote (g : Graph (Opcode G) (ports G A) [] sigs (ports G B))
    (checked : Chain G A B .entry g.toTerm) :
    (⟨A⟩ : Computations G) ⟶ (⟨B⟩ : Computations G) :=
  checked.fold (fun word => (⟨word⟩ : Computations G)) Instruction.arrow

/-- A total interpretation of the generator families. A pure generator is
a function on value tuples. An effect can also consume and return runtime. -/
structure Model (G : EffectfulPolygraph.{u, v}) where
  value : G.Obj → Type w
  runtime : Type w
  pure (e : G.pure.Edge) :
    Tuple (PortType.Val value (fun _ : PUnit.{u + 1} => runtime)) ((G.pure.source e).map .value) →
      Tuple (PortType.Val value (fun _ : PUnit.{u + 1} => runtime)) ((G.pure.target e).map .value)
  effect (e : G.effect.Edge) :
    Tuple (PortType.Val value (fun _ : PUnit.{u + 1} => runtime)) (ports G (G.effect.source e)) →
      Tuple (PortType.Val value (fun _ : PUnit.{u + 1} => runtime)) (ports G (G.effect.target e))

abbrev Model.Val (m : Model.{u, v, w} G) := PortType.Val m.value (fun _ : PUnit.{u + 1} => m.runtime)

def Model.step (m : Model.{u, v, w} G) (op : Instruction G A B) :
    Tuple m.Val (ports G A) → Tuple m.Val (ports G B) :=
  match op with
  | .pure e => fun | .cons rt data => .cons rt (m.pure e data)
  | .effect e => m.effect e

def Model.toRVSDG (m : Model.{u, v, w} G) : RVSDG.Model (Opcode G) where
  value := m.value
  state _ := m.runtime
  run := fun | .ordered op => m.step op

/-- Evaluate the composition-only interpretation in types. -/
def denoteFunctions (m : Model.{u, v, w} G) (g : Graph (Opcode G) (ports G A) [] sigs (ports G B))
    (checked : Chain G A B .entry g.toTerm) :
    Tuple m.Val (ports G A) ⟶ Tuple m.Val (ports G B) :=
  checked.fold (fun word => Tuple m.Val (ports G word)) (fun op => ↾m.step op)

/-- A functor from the presented computations which agrees with a total
generator model under its ordered tuple encoding. -/
structure Realization (m : Model.{u, v, w} G) (F : Computations G ⥤ Type (max u w)) where
  encode (A : List G.Obj) : Tuple m.Val (ports G A) ≃ F.obj ⟨A⟩
  step {A B : List G.Obj} (op : Instruction G A B) (input : Tuple m.Val (ports G A)) :
    F.map op.arrow (encode A input) = encode B (m.step op input)

end Silmaril.SSA.RVSDG.OrderedRuntime
