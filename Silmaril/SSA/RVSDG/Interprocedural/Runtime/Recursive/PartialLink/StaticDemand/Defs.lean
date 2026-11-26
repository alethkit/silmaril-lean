module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Defs

/-! # Demand through statically resolved, acyclic linked calls -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness (Demand DemandPlan selectWires)
open Continuation.Partial (Config Site)
open Continuation.Partial.Executable (Actions Observation next?)
open Silmaril.Semantics.Dataflow (GenKill)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {entry results : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

/-- An admission for acyclic RVSDG bindings and γ arms. A static application
names an entry port holding the callable and witnesses its captured values
with typed wires from the caller's entry. The callee can itself have admitted
calls. Reusing the same callee at different call sites permits different result
demands; the finite witness excludes recursive and dynamically selected targets. -/
inductive Code (Op : Dialect.{u, v} (ValueSort V S) S) :
    Ports (Ty V S) → List (Ports (Ty V S)) → List (Ports (Ty V S)) → Ports (Ty V S) → Type (max u v) where
  | ret {entry results : Ports (Ty V S)} {past : List (Ports (Ty V S))}
      (wires : Wires entry past results) : Code Op entry past [] results
  | primitive {entry results ins outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      (opcode : Op ins outs) (operands : Wires entry past ins)
      (rest : Code Op entry (past ++ [outs]) sigs results) : Code Op entry past (outs :: sigs) results
  | apply {entry results context : Ports (Ty V S)} {fn : Function V S}
      {past sigs bodySigs : List (Ports (Ty V S))}
      (target : Port entry fn.port) (captures : Wires entry [] context)
      (body : Code Op (context ++ fn.args) [] bodySigs fn.results)
      (arguments : Wires entry past fn.args)
      (rest : Code Op entry (past ++ [fn.results]) sigs results) :
      Code Op entry past (fn.results :: sigs) results
  | gamma {entry results captures outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      (extra : Nat) (armSigs : Fin (extra + 2) → List (Ports (Ty V S)))
      (selector : Origin entry past (.control (extra + 2))) (wires : Wires entry past captures)
      (arms : (i : Fin (extra + 2)) → Code Op captures [] (armSigs i) outs)
      (rest : Code Op entry (past ++ [outs]) sigs results) : Code Op entry past (outs :: sigs) results

/-- Erase the static call witnesses. The result uses the runtime's own
primitive, apply and γ nodes, with their original typed operands. -/
def Code.term : {entry results : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    Code Op entry past sigs results → NestedTheta.Term (Instruction Op) entry past sigs results
  | _, _, _, _, .ret wires => .ret wires
  | _, _, _, _, .primitive opcode operands rest =>
    .bind ⟨_, .base (.simple (.primitive opcode)), operands, fun i => i.elim0⟩ (fun i => i.elim0) rest.term
  | _, _, _, _, .apply (fn := fn) target _ _ arguments rest =>
    .bind ⟨_, .base (.simple (.apply fn)), .cons (.arg target) arguments, fun i => i.elim0⟩
      (fun i => i.elim0) rest.term
  | _, _, _, _, .gamma extra armSigs selector wires arms rest =>
    .bind ⟨_, .base (.gamma extra), .cons selector wires, armSigs⟩
      (fun i => (arms i).term) rest.term

/-- Check the static hypothesis against actual runtime values. Earlier results
may supply arguments or γ captures. The witnesses must hold for every formal
argument tuple and every γ capture tuple supplied by preceding locals. -/
def Code.Resolved : {entry results : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    Code Op entry past sigs results → Tuple m.Val entry → Prop
  | _, _, _, _, .ret _, _ => True
  | _, _, _, _, .primitive _ _ rest, input => rest.Resolved input
  | _, _, _, _, .apply target captures body _ rest, input =>
    let captured := captures.read input PUnit.unit
    input.get target = .closure captured body.term.toGraph ∧
      (∀ params, body.Resolved (prependContext params captured)) ∧ rest.Resolved input
  | _, _, past, _, .gamma _ _ _ wires arms rest, input =>
    (∀ (locals : Locals m.Val past) i, (arms i).Resolved (wires.read input locals)) ∧
      rest.Resolved input

def resultDemand (pc : Nat) (next : DemandPlan) : Demand :=
  fun p => next.live.contains (.output pc p)

def applyReads {context params : Ports (Ty V S)}
    (live : List Address) (captures : Wires entry [] context) (arguments : Wires entry past params) :
    List Address :=
  selectWires (fun _ p => live.contains (.arg p)) captures ++
    selectWires (fun _ p => live.contains (.arg (context.length + p))) arguments

/-- Backwards transfer on the shared schedule. Every primitive attempt reads
all its operands. Each application passes its result demand to the same
summary function of the statically resolved callee. A γ uses the native
transfer to join the live captures of its arms at the binding's output demand. -/
def Code.plan (demand : Demand) : {entry results : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    Code Op entry past sigs results → DemandPlan
  | _, _, past, _, .ret wires => (⟨[], []⟩ : DemandPlan).prepend past.length (selectWires demand.observes wires)
  | _, _, past, _, .primitive _ operands rest => (rest.plan demand).prepend past.length operands.addresses
  | _, _, past, _, .apply _ captures body arguments rest =>
    let next := rest.plan demand
    let live := (body.plan (resultDemand past.length next)).live
    next.prepend past.length (applyReads live captures arguments)
  | _, _, past, _, .gamma (outs := outs) extra _ selector wires arms rest =>
    let next := rest.plan demand
    let kind : NestedTheta.Kind (Instruction Op) _ outs := .base (.gamma extra)
    let reads := kind.demandReads past.length next.live (.cons selector wires)
      (fun i requested => ((arms i).plan requested).live)
    next.prepend past.length reads

def Code.liveness (code : Code Op entry [] sigs results) (demand : Demand) : GenKill Nat Address :=
  NestedTheta.Liveness.problem (code.plan demand).reads

/-- Executable entry summary, indexed by demand on returned ports (returned
state ports are always observed). -/
def Code.liveIn (code : Code Op entry [] sigs results) (demand : Demand) : List Address :=
  (code.plan demand).live.eraseDups

def Code.AgreesOnInputs (code : Code Op entry [] sigs results) (demand : Demand)
    (left right : Tuple m.Val entry) : Prop :=
  ∀ {ty} (p : Port entry ty), .arg p.index ∈ code.liveIn demand → left.get p = right.get p

/-- Lockstep under the actual runner transitions. At a block, the checked
continuation can be supplied any common hypothetical primitive result and
store. Its behavior can include another block, with the same guarantee. -/
inductive Matches (actions : Actions m σ) (demand : Demand) :
    Config m σ results → Config m σ results → Prop where
  | returned {left right : Tuple m.Val results} {store : σ} (agree : demand.Agrees left right) :
      Matches actions demand ⟨.returned left .halt, store⟩ ⟨.returned right .halt, store⟩
  | step {left right nextL nextR : Config m σ results}
      (stepL : next? actions left = some nextL) (stepR : next? actions right = some nextR)
      (later : Matches actions demand nextL nextR) : Matches actions demand left right
  | blocked {site : Site m} {left right : Continuation.Stack m site.outs results} {store : σ}
      (undefined : (actions.step site.opcode site.input).run store = none)
      (resume : ∀ value nextStore, Matches actions demand
        ⟨.returned value left, nextStore⟩ ⟨.returned value right, nextStore⟩) :
      Matches actions demand ⟨.eval site.job left, store⟩ ⟨.eval site.job right, store⟩

/-- Settled observations expose equal returned stores, or the very same
typed attempt and store with behaviorally related saved continuations. -/
inductive EndpointsAgree (actions : Actions m σ) (demand : Demand) :
    Observation m σ results → Observation m σ results → Prop where
  | returned {left right : Tuple m.Val results} {store : σ} (agree : demand.Agrees left right) :
      EndpointsAgree actions demand (.returned left store) (.returned right store)
  | blocked {site : Site m} {left right : Continuation.Stack m site.outs results} {store : σ}
      (resume : ∀ value nextStore, Matches actions demand
        ⟨.returned value left, nextStore⟩ ⟨.returned value right, nextStore⟩) :
      EndpointsAgree actions demand (.blocked ⟨site, left⟩ store) (.blocked ⟨site, right⟩ store)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand
