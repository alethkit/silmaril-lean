module

public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Denotation

/-! Native observations of pure single loops over a fixed data-sort alphabet. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Institution

open CategoryTheory Silmaril.Logic.Institution
open Diamond (Model Ty Val ValueSort dataPorts)
open Diamond.Institution (Signature mapDataflow)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P Q : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}

/-- Relabel the two producer tables and keep all wires and both Phi columns. -/
def mapGraph (h : P ⟶ Q) (g : Graph P.op inputs carried entrySigs headerSigs out) :
    Graph Q.op inputs carried entrySigs headerSigs out :=
  ⟨mapDataflow h g.preheader, mapDataflow h g.header, g.phiInputs, g.predicate, g.result⟩

/-- A loop with a typed boundary and its own internal producer and latch profiles. -/
structure Program (P : Signature.{u, v} Data) (inputs : List (ValueSort Data))
    (out : ValueSort Data) where
  carried : List (ValueSort Data)
  entrySigs : List (List (Ty Data))
  headerSigs : List (List (Ty Data))
  graph : Graph P.op inputs carried entrySigs headerSigs out

def Program.map (h : P ⟶ Q) (p : Program P inputs out) : Program Q inputs out :=
  ⟨p.carried, p.entrySigs, p.headerSigs, mapGraph h p.graph⟩

/-- Two loops may have different internal profiles and must have identical typed boundaries. -/
structure Equation (P : Signature.{u, v} Data) where
  inputs : List (ValueSort Data)
  out : ValueSort Data
  lhs : Program P inputs out
  rhs : Program P inputs out

/-- Partial equality accepts two divergences, rejects a return on only one side,
and compares the results when both return. -/
def Equation.Holds (e : Equation P) (m : Model.{u, v, w} P.op) : Prop :=
  ∀ input : Tuple (Val m.value) (dataPorts e.inputs),
    e.lhs.graph.denote m input = e.rhs.graph.denote m input

/-- Sentences observe partial equality or assert termination on every input. -/
inductive Sentence (P : Signature.{u, v} Data) where
  | equation (e : Equation P)
  | terminates {inputs : List (ValueSort Data)} {out : ValueSort Data} (p : Program P inputs out)

def Sentence.map (h : P ⟶ Q) : Sentence P → Sentence Q
  | .equation e => .equation ⟨e.inputs, e.out, e.lhs.map h, e.rhs.map h⟩
  | .terminates p => .terminates (p.map h)

def Sentence.Holds (s : Sentence P) (m : Model.{u, v, w} P.op) : Prop :=
  match s with
  | .equation e => e.Holds m
  | .terminates (inputs := inputs) p =>
    ∀ input : Tuple (Val m.value) (dataPorts inputs), (p.graph.denote m input).Dom

/-- The source room uses the same discrete total primitive models as the diamond. -/
def room (P : Signature.{u, v} Data) :
    Room.{max u v, max u v (w + 1), max u v (w + 1)} where
  Sen := Sentence P
  Mod := Cat.of (Discrete (Model.{u, v, w} P.op))
  Sat m s := s.Holds m.as

end Silmaril.SSA.SeaOfNodes.Loop.Institution
