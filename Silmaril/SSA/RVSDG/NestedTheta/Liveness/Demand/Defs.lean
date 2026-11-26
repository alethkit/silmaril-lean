module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Defs
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Logic.Function.Iterate

/-! # Backwards liveness with demanded γ and θ results -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta

open Silmaril.Semantics.Dataflow

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

namespace Liveness

abbrev Demand := Nat → Bool

/-- A region observes every returned state port along with the requested positions. -/
def Demand.observes (demand : Demand) : PortType V S → Nat → Bool
  | .state _, _ => true
  | _, i => demand i

/-- Read the typed origins of the selected user ports, in user-port order. -/
def selectWires {Ty : Type u} {entry : Ports Ty} {scope : List (Ports Ty)} :
    (Ty → Nat → Bool) → {users : Ports Ty} → Wires entry scope users → List Address
  | _, _, .nil => []
  | selected, _, .cons (t := ty) source rest =>
    (if selected ty 0 then [source.address] else []) ++
      selectWires (fun t i => selected t (i + 1)) rest

/-- The selected reads and their live-in set are computed together using the
same local gen/kill transfer as the unconditional schedule. -/
structure DemandPlan where
  reads : List (List Address)
  live : List Address

def DemandPlan.prepend (next : DemandPlan) (pc : Nat) (reads : List Address) : DemandPlan :=
  ⟨reads :: next.reads, transfer pc reads next.live⟩

/-- Equality at the demanded result ports, including state. -/
def Demand.Agrees {F : PortType V S → Type w} (demand : Demand)
    (left right : Tuple F outs) : Prop :=
  ∀ {ty} (port : Port outs ty), demand.observes ty port.index = true → left.get port = right.get port

/-- Bounded observations either both lack a return or agree on the demanded result. -/
inductive Demand.ResultAgrees {F : PortType V S → Type w} (demand : Demand) :
    Option (Tuple F outs) → Option (Tuple F outs) → Prop
  | none : ResultAgrees demand none none
  | some {left right} : demand.Agrees left right → ResultAgrees demand (some left) (some right)

namespace Feedback

abbrev Mask (arity : Nat) := Finset (Fin arity)

def includes {arity : Nat} (live : Mask arity) (port : Nat) : Bool :=
  if valid : port < arity then decide (⟨port, valid⟩ ∈ live) else false

/-- Body result zero is the continuation predicate. At later ports demand
either the exit result or the corresponding input of the next activation.
The body analysis also demands every returned state port. -/
def bodyDemand {arity : Nat} (exit : Demand) (live : Mask arity) : Demand
  | 0 => true
  | i + 1 => exit i || includes live i

/-- Follow demanded body result wires backwards and extract the resulting
live argument origins in the typed carried signature. -/
def step {arity : Nat} (exit : Demand) (analyzeBody : Demand → List Address)
    (live : Mask arity) : Mask arity :=
  let needed := analyzeBody (bodyDemand exit live)
  Finset.univ.filter fun p => Address.arg p.val ∈ needed

/-- The Kleene iteration starts at the empty carried mask. A strict increase
adds a port, so the number of carried ports bounds the number of rounds. -/
def close {arity : Nat} (exit : Demand) (analyzeBody : Demand → List Address) : Mask arity :=
  (step exit analyzeBody)^[arity] ∅

/-- Agreement at the live carried input positions of one θ activation. -/
def Agrees {F : PortType V S → Type w} {carried : Ports (PortType V S)}
    (live : Mask carried.length) (left right : Tuple F carried) : Prop :=
  ∀ {ty} (port : Port carried ty), includes live port.index = true → left.get port = right.get port

end Feedback

end Liveness

open Liveness

/-- A γ reads its selector and the captures required by any arm at the current
output demand. A θ reads the carried inputs in its feedback fixed point.
Primitive bindings read all their input wires. -/
def Kind.demandReads (pc : Nat) (next : List Address) :
    {ins out : Ports (PortType V S)} → (kind : Kind Op ins out) →
    Wires args past ins → (Fin kind.arity → Demand → List Address) → List Address
  | _, _, .base (.simple _), wires, _ => wires.addresses
  | _, _, .theta carried, wires, body =>
    let live : Feedback.Mask carried.length :=
      Feedback.close (fun p => next.contains (.output pc p)) (body (0 : Fin 1))
    selectWires (fun _ p => Feedback.includes live p) wires
  | _, _, .base (.gamma _), .cons selector captures, arm =>
    let needed := (List.ofFn fun i => arm i (fun p => next.contains (.output pc p))).flatten
    selector.address :: selectWires (fun _ p => needed.contains (.arg p)) captures

/-- Propagate demand backwards through the existing numbered origins. Each γ
arm is analyzed at the binding's output demand, and θ closes demand over its
body's typed result and feedback wires. -/
def Term.demandPlan (demand : Demand) {args outs : Ports (PortType V S)}
    {past sigs : List (Ports (PortType V S))} (term : Term Op args past sigs outs) : DemandPlan :=
  match term with
  | .ret results => (⟨[], []⟩ : DemandPlan).prepend past.length (selectWires demand.observes results)
  | .bind node children rest =>
    let next := rest.demandPlan demand
    let reads := node.kind.demandReads past.length next.live node.inputs
      (fun i requested => ((children i).demandPlan requested).live)
    next.prepend past.length reads
termination_by structural term

/-- The live carried inputs for a θ body and a requested exit demand. -/
def Term.feedbackLive {carried : Ports (PortType V S)}
    (body : Term Op carried [] sigs (Theta.BodyResults carried)) (exit : Demand) :
    Feedback.Mask carried.length :=
  Feedback.close exit (fun demand => (body.demandPlan demand).live)

/-- Shared gen/kill equations after specializing the structured reads to this demand. -/
def Graph.demandLiveness (g : Graph Op args [] sigs outs) (demand : Demand) : GenKill Nat Address :=
  problem (g.toTerm.demandPlan demand).reads

/-- Executable origins live at entry for the requested output positions and state. -/
def Graph.demandLiveIn (g : Graph Op args [] sigs outs) (demand : Demand) : List Address :=
  (g.toTerm.demandPlan demand).live.eraseDups

/-- Typed inputs agree at the positions in the shared demand-specialized solution. -/
def Graph.AgreesOnDemandInputs (g : Graph Op args [] sigs outs) (demand : Demand)
    {F : PortType V S → Type w} (left right : Tuple F args) : Prop :=
  ∀ {ty} (port : Port args ty), .arg port.index ∈ (g.demandLiveness demand).mayOut 0 →
    left.get port = right.get port

/-- A finite observation of the demanded positions and exact returned state. -/
def Graph.ReturnsDemand (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (demand : Demand) (input : Tuple m.Val args) (expected : Tuple m.Val outs) : Prop :=
  ∃ out, g.Returns m input out ∧ demand.Agrees out expected

end Silmaril.SSA.RVSDG.NestedTheta
