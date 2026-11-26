module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Defs

/-! # Backwards liveness with demanded γ results -/

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

end Liveness

open Liveness

/-- A γ reads its selector and the captures required by any arm at the current
output demand. Primitive and θ inputs are kept in full. -/
def Kind.demandReads (pc : Nat) (next : List Address) :
    {ins out : Ports (PortType V S)} → (kind : Kind Op ins out) →
    Wires args past ins → (Fin kind.arity → Demand → List Address) → List Address
  | _, _, .base (.simple _), wires, _ => wires.addresses
  | _, _, .theta _, wires, _ => wires.addresses
  | _, _, .base (.gamma _), .cons selector captures, arm =>
    let needed := (List.ofFn fun i => arm i (fun p => next.contains (.output pc p))).flatten
    selector.address :: selectWires (fun _ p => needed.contains (.arg p)) captures

/-- Propagate demand backwards through the existing numbered origins. Each γ
arm gets a fresh local analysis at the demand on the binding's output ports. -/
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

/-- Shared gen/kill equations after specializing the γ reads to this demand. -/
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
