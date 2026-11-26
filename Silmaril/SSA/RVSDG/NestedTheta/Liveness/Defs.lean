module

public import Silmaril.Semantics.Dataflow.GenKill
public import Silmaril.SSA.RVSDG.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Defs

/-! # Same-region liveness for a numbered γ/θ graph -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta

open Silmaril.Semantics.Dataflow

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

namespace Liveness

/-- All output ports of a vertex are defined together when it finishes. -/
def definedAt (pc : Nat) : Address → Bool
  | .arg _ => false
  | .output vertex _ => vertex == pc

/-- Program point `pc` is immediately before binding `pc`. The last point
reads the result wires, and the remaining points have no reads. -/
def problem (reads : List (List Address)) : GenKill Nat Address where
  nbrs pc := {pc + 1}
  gen pc := {address | address ∈ (reads.drop pc).headD []}
  kill pc := {address | definedAt pc address}

/-- Evaluate the same gen/kill transfer backwards over the finite suffix. -/
def sweep : List (List Address) → Nat → List Address
  | [], _ => []
  | reads :: rest, pc => reads ++ (sweep rest (pc + 1)).filter (fun a => !definedAt pc a)

end Liveness

/-- One row of uses per local binding, followed by the result uses. Structured
vertices read every input wire. Each child has a separate local schedule. -/
def Term.readSchedule : {past sigs : List (Ports (PortType V S))} →
    Term Op args past sigs outs → List (List Address)
  | _, _, .ret results => [results.addresses]
  | _, _, .bind node _ rest => node.inputs.addresses :: rest.readSchedule

/-- Standard backward may-liveness on the existing typed numbered graph. -/
def Graph.liveness (g : Graph Op args [] sigs outs) : GenKill Nat Address :=
  Liveness.problem g.toTerm.readSchedule

/-- The live origins before a binding or return, using local wire addresses.
Points beyond the return have no live origins. -/
def Graph.liveAt (g : Graph Op args [] sigs outs) (pc : Nat) : List Address :=
  (Liveness.sweep (g.toTerm.readSchedule.drop pc) pc).eraseDups

/-- A typed client of the shared analysis. Agreement is required on live
entry ports, including any live selectors and runtime tokens. -/
def Graph.AgreesOnLiveInputs (g : Graph Op args [] sigs outs)
    {F : PortType V S → Type w} (left right : Tuple F args) : Prop :=
  ∀ {ty} (port : Port args ty), .arg port.index ∈ g.liveness.mayOut 0 →
    left.get port = right.get port

end Silmaril.SSA.RVSDG.NestedTheta
