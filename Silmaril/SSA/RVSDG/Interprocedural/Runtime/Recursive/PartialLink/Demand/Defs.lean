module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Defs

/-! # Demand across one statically wired linked application -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand

open NestedTheta.Liveness (Demand selectWires)
open Continuation (Stack)
open Continuation.Partial (Site)
open Continuation.Partial.Executable (Actions Observation runFor)
open Silmaril.Semantics.Dataflow (GenKill)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports : Ports (Ty V S)} {caller callee : Function V S}

/-- A two-λ module with a statically wired application. The first λ binds a
primitive and returns its wired results. The exported λ captures that callable,
passes a typed tuple of its arguments, and returns through its own result wires. -/
structure DirectCall (Op : Dialect.{u, v} (ValueSort V S) S)
    (imports : Ports (Ty V S)) (caller callee : Function V S) where
  context : Ports (Ty V S)
  captures : Wires imports [] context
  ins : Ports (Ty V S)
  outs : Ports (Ty V S)
  opcode : Op ins outs
  operands : Wires (context ++ callee.args) [] ins
  calleeResults : Wires (context ++ callee.args) [outs] callee.results
  arguments : Wires caller.args [] callee.args
  callerResults : Wires caller.args [callee.results] caller.results

namespace DirectCall

variable (call : DirectCall Op imports caller callee)

/-- Lift the caller's wires past its captured callable. -/
def withCallable {past users : Ports (Ty V S)} {scope : List (Ports (Ty V S))}
    (callee : Function V S) (wires : Wires past scope users) :
    Wires (callee.port :: past) scope users :=
  wires.map fun _ edge => match edge with
    | .arg p => .arg (.tail p)
    | .output i p => .output i p

def calleeTail : NestedTheta.Term (Instruction Op) (call.context ++ callee.args) [call.outs] [] callee.results :=
  .ret call.calleeResults

def calleeBody : NestedTheta.Term (Instruction Op) (call.context ++ callee.args) [] [call.outs] callee.results :=
  .bind ⟨call.ins, .base (.simple (.primitive call.opcode)), call.operands, fun i => i.elim0⟩
    (fun i => i.elim0) call.calleeTail

def callerTail : NestedTheta.Term (Instruction Op)
    (callee.port :: caller.args) [callee.results] [] caller.results :=
  .ret (withCallable callee call.callerResults)

def callerBody : NestedTheta.Term (Instruction Op)
    (callee.port :: caller.args) [] [callee.results] caller.results :=
  .bind ⟨callee.port :: callee.args, .base (.simple (.apply callee)),
    .cons (.arg .head) (withCallable callee call.arguments), fun i => i.elim0⟩
    (fun i => i.elim0) call.callerTail

/-- Lower the admission by construction to the existing actual ω graph. -/
def graph : Omega Op imports [caller.port] [[callee.port], [caller.port]] :=
  OmegaTerm.toGraph ⟨.bind (.lambda ⟨call.context, call.captures, [call.outs], call.calleeBody⟩)
    (.bind (.lambda ⟨[callee.port], .cons (.output (0 : Fin 1) .head) .nil,
      [callee.results], call.callerBody⟩)
      (.ret (.cons (.output (1 : Fin 2) .head) .nil)))⟩

/-- Origins which supply the demanded caller results. -/
def resultOrigins (demand : Demand) : List Address :=
  selectWires demand.observes call.callerResults

/-- Only requested results that come from the call demand a callee result. -/
def calleeDemand (demand : Demand) : Demand :=
  fun p => (call.resultOrigins demand).contains (.output 0 p)

def calleeLiveness (demand : Demand) : GenKill Nat Address :=
  call.calleeBody.toGraph.demandLiveness (call.calleeDemand demand)

def calleeLiveIn (demand : Demand) : List Address :=
  call.calleeBody.toGraph.demandLiveIn (call.calleeDemand demand)

/-- Read live captured ports through the actual module capture wires. -/
def liveImports (demand : Demand) : List Address :=
  let live := call.calleeLiveIn demand
  (selectWires (fun _ p => live.contains (.arg p)) call.captures).eraseDups

/-- Join direct result reads with live formal parameters mapped through the
call argument wires. Captures occupy the earlier callee entry positions. -/
def liveArguments (demand : Demand) : List Address :=
  let live := call.calleeLiveIn demand
  let direct := (call.resultOrigins demand).filter fun a => match a with
    | .arg _ => true
    | .output _ _ => false
  (direct ++ selectWires (fun _ p => live.contains (.arg (call.context.length + p)))
    call.arguments).eraseDups

def AgreesOnInputs (demand : Demand) (importsL importsR : Tuple m.Val imports)
    (argsL argsR : Tuple m.Val caller.args) : Prop :=
  (∀ {ty} (p : Port imports ty), .arg p.index ∈ call.liveImports demand →
    importsL.get p = importsR.get p) ∧
  ∀ {ty} (p : Port caller.args ty), .arg p.index ∈ call.liveArguments demand →
    argsL.get p = argsR.get p

/-- Execute the actual linked export through the existing runner. -/
def run (actions : Actions m σ) (fuel unitId : Nat)
    (imported : Tuple m.Val imports) (arguments : Tuple m.Val caller.args) (store : σ) :
    Except (Failure m σ) (Observation m σ caller.results) :=
  Executable.run actions fuel unitId call.graph imported .head arguments store

end DirectCall

/-- Corresponding saved stacks give matching demanded observations when
supplied a common hypothetical result and store. This is a statement about
the saved continuation's behavior. -/
def SavedAgrees {ports results : Ports (Ty V S)} (actions : Actions m σ) (demand : Demand)
    (left right : Stack m ports results) : Prop :=
  ∀ (value : Tuple m.Val ports) (store : σ), ∃ fuel outL outR,
    (runFor actions fuel ⟨.returned value left, store⟩).result = some (outL, store) ∧
    (runFor actions fuel ⟨.returned value right, store⟩).result = some (outR, store) ∧
    demand.Agrees outL outR

/-- At a settled invocation boundary, both observations return with the
same store or block at exactly the same typed attempt and store. -/
inductive ObservationsAgree {results : Ports (Ty V S)} (actions : Actions m σ) (demand : Demand) :
    Observation m σ results → Observation m σ results → Prop
  | returned {left right store} : demand.Agrees left right →
      ObservationsAgree actions demand (.returned left store) (.returned right store)
  | blocked {site : Site m} {left right : Stack m site.outs results} {store} :
      SavedAgrees actions demand left right →
      ObservationsAgree actions demand (.blocked ⟨site, left⟩ store) (.blocked ⟨site, right⟩ store)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand
