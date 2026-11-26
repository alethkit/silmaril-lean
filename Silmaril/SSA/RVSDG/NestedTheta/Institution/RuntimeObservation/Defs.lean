module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs

/-! Partial observations of numbered nested graphs with total primitive interpretations. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation

open CategoryTheory Silmaril.Logic.Institution

universe u v w

variable {V S : Type u} {P Q : RVSDG.Institution.Signature.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- A numbered graph at a fixed boundary with its own ordered producer signatures. -/
structure Program (P : RVSDG.Institution.Signature.{u, v} V S) (args outs : Ports (PortType V S)) where
  sigs : List (Ports (PortType V S))
  graph : Graph P.op args [] sigs outs

def Program.map (h : P ⟶ Q) (p : Program P args outs) : Program Q args outs :=
  ⟨p.sigs, Institution.mapGraph (RVSDG.Institution.Signature.opcodeMap h) p.graph⟩

/-- Partial equations compare whole result tuples. Termination is a separate sentence. -/
inductive Sentence (P : RVSDG.Institution.Signature.{u, v} V S) where
  | equation {args outs : Ports (PortType V S)} (lhs rhs : Program P args outs)
  | terminates {args outs : Ports (PortType V S)} (p : Program P args outs)

def Sentence.map (h : P ⟶ Q) : Sentence P → Sentence Q
  | .equation lhs rhs => .equation (lhs.map h) (rhs.map h)
  | .terminates p => .terminates (p.map h)

/-- Observe the actual partial θ interpretation, embedding each total leaf into Part. -/
noncomputable def observe (m : RVSDG.Model.{u, v, w} P.op) (g : Graph P.op args [] sigs outs)
    (input : Tuple m.Val args) : Part (Tuple m.Val outs) :=
  Partial.observe (MonadicModel.ofRuntime m) g input

def Sentence.Holds (s : Sentence P) (m : RVSDG.Model.{u, v, w} P.op) : Prop :=
  match s with
  | .equation (args := args) lhs rhs =>
    ∀ input : Tuple m.Val args, observe m lhs.graph input = observe m rhs.graph input
  | .terminates (args := args) p =>
    ∀ input : Tuple m.Val args, (observe m p.graph input).Dom

/-- The room over the same discrete runtime models as ordinary RVSDG. -/
def room (P : RVSDG.Institution.Signature.{u, v} V S) :
    Room.{max u v, max u v (w + 1), max u v (w + 1)} where
  Sen := Sentence P
  Mod := Cat.of (Discrete (RVSDG.Model.{u, v, w} P.op))
  Sat m s := s.Holds m.as

end Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation
