module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Wiring

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand.Proofs

open NestedTheta.Liveness (Demand selectWires transfer)
open NestedTheta.Liveness.Demand.Proofs (ScopeAgrees valueAt read_all read_selected)
open Continuation (Stack)
open Continuation.Partial (Site Config)
open Continuation.Partial.Executable (Actions Observation runFor next? observe)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports : Ports (Ty V S)} {caller callee : Function V S}
variable (call : DirectCall Op imports caller callee)

private def calleeValue (entry : Tuple m.Val imports) : m.Val callee.port :=
  .closure (call.captures.read entry PUnit.unit) call.calleeBody.toGraph

private def callerEntry (entry : Tuple m.Val imports) (args : Tuple m.Val caller.args) :
    Tuple m.Val (callee.port :: caller.args) :=
  .cons (calleeValue call entry) args

private def calleeEntry (entry : Tuple m.Val imports) (args : Tuple m.Val caller.args) :
    Tuple m.Val (call.context ++ callee.args) :=
  prependContext
    ((DirectCall.withCallable callee call.arguments).read (callerEntry call entry args) PUnit.unit)
    (call.captures.read entry PUnit.unit)

private def primitiveInput (entry : Tuple m.Val imports) (args : Tuple m.Val caller.args) :
    Tuple m.Val call.ins :=
  call.operands.read (calleeEntry call entry args) PUnit.unit

private def site (input : Tuple m.Val call.ins) : Site m :=
  ⟨call.ins, call.outs, call.opcode, fun i => i.elim0, fun i => i.elim0, input⟩

private def saved (entry : Tuple m.Val imports) (args : Tuple m.Val caller.args) :
    Stack m call.outs caller.results :=
  .resume (past := []) call.calleeTail (calleeEntry call entry args) PUnit.unit
    (.resume (past := []) call.callerTail (callerEntry call entry args) PUnit.unit .halt)

private def finish (entry : Tuple m.Val imports) (args : Tuple m.Val caller.args)
    (value : Tuple m.Val call.outs) : Tuple m.Val caller.results :=
  let returned := call.calleeResults.read (calleeEntry call entry args) (value, PUnit.unit)
  (DirectCall.withCallable callee call.callerResults).read (callerEntry call entry args)
    (returned, PUnit.unit)

private theorem read_withCallable {entry users : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (wires : Wires entry past users) (cv : m.Val callee.port) (args : Tuple m.Val entry)
    (locals : Locals m.Val past) :
    (DirectCall.withCallable callee wires).read (.cons cv args) locals = wires.read args locals := by
  induction wires with
  | nil => rfl
  | cons origin rest ih =>
    cases origin <;> exact congrArg (Tuple.cons _) ih

private theorem prepend_agrees {Ty : Type u} {F : Ty → Type w} {context params : Ports Ty}
    (wanted : Nat → Prop) (capsL capsR : Tuple F context) (argsL argsR : Tuple F params)
    (cap : ∀ {ty} (p : Port context ty), wanted p.index → capsL.get p = capsR.get p)
    (arg : ∀ {ty} (p : Port params ty), wanted (context.length + p.index) → argsL.get p = argsR.get p) :
    ∀ {ty} (p : Port (context ++ params) ty), wanted p.index →
      (prependContext argsL capsL).get p = (prependContext argsR capsR).get p := by
  induction capsL generalizing wanted with
  | nil =>
    cases capsR
    intro ty p live
    exact arg p (by simpa only [List.length_nil, Nat.zero_add] using live)
  | cons x xs ih =>
    cases capsR with
    | cons y ys =>
      intro ty p live
      cases p with
      | head => exact cap .head live
      | tail p =>
        apply ih (fun i => wanted (i + 1)) ys
        · exact fun p live => cap (.tail p) live
        · intro ty p live
          exact arg p (by simpa only [List.length_cons, Nat.succ_add] using live)
        · exact live

private theorem leaf_live (demand : Demand) (a : Address) :
    a ∈ call.calleeLiveIn demand ↔ a ∈ (call.calleeBody.demandPlan (call.calleeDemand demand)).live := by
  simp only [DirectCall.calleeLiveIn, NestedTheta.Graph.demandLiveIn,
    NestedTheta.Term.toTerm_toGraph, List.mem_eraseDups]

private theorem leaf_agrees (demand : Demand) (importsL importsR : Tuple m.Val imports)
    (argsL argsR : Tuple m.Val caller.args) (agree : call.AgreesOnInputs demand importsL importsR argsL argsR) :
    ScopeAgrees (scope := []) (call.calleeBody.demandPlan (call.calleeDemand demand)).live
      (calleeEntry call importsL argsL) (calleeEntry call importsR argsR) PUnit.unit PUnit.unit := by
  intro ty edge live
  cases edge with
  | output i _ => exact i.elim0
  | arg p =>
    have needed := (leaf_live call demand _).2 live
    simp only [valueAt, calleeEntry, callerEntry]
    rw [read_withCallable call.arguments (calleeValue call importsL) argsL PUnit.unit,
      read_withCallable call.arguments (calleeValue call importsR) argsR PUnit.unit]
    apply prepend_agrees (fun i => Address.arg i ∈ call.calleeLiveIn demand)
    · intro ty p present
      apply read_selected (fun _ i => (call.calleeLiveIn demand).contains (.arg i)) call.captures
      · intro ty edge selected
        cases edge with
        | output i _ => exact i.elim0
        | arg p => exact agree.1 p (List.mem_eraseDups.2 selected)
      · exact List.contains_iff_mem.2 present
    · intro ty p present
      apply read_selected (fun _ i => (call.calleeLiveIn demand).contains (.arg (call.context.length + i)))
        call.arguments
      · intro ty edge selected
        cases edge with
        | output i _ => exact i.elim0
        | arg p => exact agree.2 p (List.mem_eraseDups.2 (List.mem_append_right _ selected))
      · exact List.contains_iff_mem.2 present
    · exact needed

private theorem primitiveInput_agrees (demand : Demand) {importsL importsR : Tuple m.Val imports}
    {argsL argsR : Tuple m.Val caller.args} (agree : call.AgreesOnInputs demand importsL importsR argsL argsR) :
    primitiveInput call importsL argsL = primitiveInput call importsR argsR := by
  have reads : ScopeAgrees (scope := []) call.operands.addresses (calleeEntry call importsL argsL)
      (calleeEntry call importsR argsR) PUnit.unit PUnit.unit := fun edge present =>
    leaf_agrees call demand importsL importsR argsL argsR agree edge (List.mem_append_left _ present)
  exact read_all call.operands reads

private theorem finish_agrees (demand : Demand) {importsL importsR : Tuple m.Val imports}
    {argsL argsR : Tuple m.Val caller.args} (agree : call.AgreesOnInputs demand importsL importsR argsL argsR)
    (value : Tuple m.Val call.outs) :
    demand.Agrees (finish call importsL argsL value) (finish call importsR argsR value) := by
  let resultL := call.calleeResults.read (calleeEntry call importsL argsL) (value, PUnit.unit)
  let resultR := call.calleeResults.read (calleeEntry call importsR argsR) (value, PUnit.unit)
  have returns : (call.calleeDemand demand).Agrees resultL resultR := by
    intro ty p needed
    apply read_selected (call.calleeDemand demand).observes call.calleeResults _ p needed
    intro ty edge selected
    cases edge with
    | output => rfl
    | arg p =>
      apply leaf_agrees call demand importsL importsR argsL argsR agree (.arg p)
      simp only [DirectCall.calleeBody, DirectCall.calleeTail, NestedTheta.Term.demandPlan,
        NestedTheta.Liveness.DemandPlan.prepend, transfer, List.filter_nil, List.append_nil,
        List.mem_append, List.mem_filter]
      exact Or.inr ⟨selected, rfl⟩
  intro ty p needed
  have readL := congrArg (fun values : Tuple m.Val caller.results => values.get p)
    (read_withCallable call.callerResults (calleeValue call importsL) argsL (resultL, PUnit.unit))
  have readR := congrArg (fun values : Tuple m.Val caller.results => values.get p)
    (read_withCallable call.callerResults (calleeValue call importsR) argsR (resultR, PUnit.unit))
  refine readL.trans (Eq.trans ?_ readR.symm)
  apply read_selected demand.observes call.callerResults _ p needed
  intro ty edge selected
  cases edge with
  | arg p =>
    exact agree.2 p (List.mem_eraseDups.2 (List.mem_append_left _
      (List.mem_filter.2 ⟨selected, rfl⟩)))
  | output i p =>
    obtain rfl := Fin.eq_zero i
    apply returns p
    cases ty with
    | state => rfl
    | value | control => exact List.contains_iff_mem.2 selected

private def initial (entry : Tuple m.Val imports) (args : Tuple m.Val caller.args) (store : σ) :
    Config m σ caller.results :=
  ⟨Continuation.start (.call (.closure (.cons (calleeValue call entry) .nil) call.callerBody.toGraph) args), store⟩

private def atAttempt (entry : Tuple m.Val imports) (args : Tuple m.Val caller.args) (store : σ) :
    Config m σ caller.results :=
  ⟨.eval (site call (primitiveInput call entry args)).job (saved call entry args), store⟩

private theorem link_start (actions : Actions m σ) (unitId : Nat) (entry : Tuple m.Val imports)
    (args : Tuple m.Val caller.args) (store : σ) :
    Executable.start actions unitId call.graph entry .head args store = .ok (initial call entry args store) := rfl

private theorem reaches_attempt (actions : Actions m σ) (entry : Tuple m.Val imports)
    (args : Tuple m.Val caller.args) (store : σ) :
    runFor actions 5 (initial call entry args store) = atAttempt call entry args store := by
  let callerStart : Config m σ caller.results :=
    ⟨.eval (.region (past := []) call.callerBody (callerEntry call entry args) PUnit.unit) .halt, store⟩
  let frame : Stack m callee.results caller.results :=
    .resume (past := []) call.callerTail (callerEntry call entry args) PUnit.unit .halt
  let calleeStart : Config m σ caller.results :=
    ⟨.eval (.region (past := []) call.calleeBody (calleeEntry call entry args) PUnit.unit) frame, store⟩
  have enterCaller : runFor actions 1 (initial call entry args store) = callerStart :=
    congrArg (fun body => (⟨.eval (.region (past := []) body (callerEntry call entry args)
      PUnit.unit) .halt, store⟩ : Config m σ caller.results))
      (NestedTheta.Term.toTerm_toGraph call.callerBody)
  have enterCallee : runFor actions 3 callerStart = calleeStart :=
    congrArg (fun body => (⟨.eval (.region (past := []) body (calleeEntry call entry args)
      PUnit.unit) frame, store⟩ : Config m σ caller.results))
      (NestedTheta.Term.toTerm_toGraph call.calleeBody)
  calc
    _ = runFor actions 4 (runFor actions 1 (initial call entry args store)) :=
      Continuation.Partial.Executable.runFor_add actions 1 4 _
    _ = runFor actions 4 callerStart := congrArg _ enterCaller
    _ = runFor actions 1 (runFor actions 3 callerStart) :=
      Continuation.Partial.Executable.runFor_add actions 3 1 _
    _ = atAttempt call entry args store := (congrArg (runFor actions 1) enterCallee).trans rfl

private theorem resumes (actions : Actions m σ) (entry : Tuple m.Val imports) (args : Tuple m.Val caller.args)
    (value : Tuple m.Val call.outs) (store : σ) :
    runFor actions 4 ⟨.returned value (saved call entry args), store⟩ =
      ⟨.returned (finish call entry args value) .halt, store⟩ := rfl

private theorem stays {ports : Ports (Ty V S)} (actions : Actions m σ) (config : Config m σ ports)
    (stopped : next? actions config = none) (fuel : Nat) : runFor actions fuel config = config := by
  cases fuel with
  | zero => rfl
  | succ => simp only [runFor, stopped]

private theorem settles (actions : Actions m σ) (unitId more : Nat) (entry : Tuple m.Val imports)
    (args : Tuple m.Val caller.args) (store : σ) :
    call.run actions (10 + more) unitId entry args store =
      .ok (match (actions.step call.opcode (primitiveInput call entry args)).run store with
        | none => .blocked ⟨site call (primitiveInput call entry args), saved call entry args⟩ store
        | some (value, middle) => .returned (finish call entry args value) middle) := by
  unfold DirectCall.run Executable.run
  rw [link_start call]
  change Except.ok (observe actions (runFor actions (10 + more) (initial call entry args store))) = _
  rw [show 10 + more = 5 + (5 + more) by omega, Continuation.Partial.Executable.runFor_add,
    reaches_attempt call]
  let attemptConfig := atAttempt call entry args store
  have step : next? actions attemptConfig =
      ((actions.step call.opcode (primitiveInput call entry args)).run store).map fun (value, middle) =>
        ⟨.returned value (saved call entry args), middle⟩ := rfl
  cases tried : (actions.step call.opcode (primitiveInput call entry args)).run store with
  | none =>
    have stopped : next? actions attemptConfig = none := by rw [step, tried]; rfl
    rw [stays actions _ stopped]
    apply congrArg Except.ok
    apply Continuation.Partial.Executable.observe_blocked.2
    refine ⟨rfl, rfl, ?_⟩
    change Part.ofOption ((actions.step call.opcode (primitiveInput call entry args)).run store) = Part.none
    rw [tried]
    rfl
  | some result =>
    obtain ⟨value, middle⟩ := result
    have completed : runFor actions 5 attemptConfig =
        ⟨.returned (finish call entry args value) .halt, middle⟩ := by
      rw [runFor, step, tried]
      exact resumes call actions entry args value middle
    rw [Continuation.Partial.Executable.runFor_add, completed, stays actions _ rfl]
    exact congrArg Except.ok (Continuation.Partial.Executable.observe_returned.2 rfl)

theorem liveIn_iff (demand : Demand) (a : Address) :
    a ∈ call.calleeLiveIn demand ↔ a ∈ (call.calleeLiveness demand).mayOut 0 :=
  call.calleeBody.toGraph.mem_demandLiveIn_iff (call.calleeDemand demand) a

theorem run_agrees (actions : Actions m σ) (unitId more : Nat) (demand : Demand)
    (importsL importsR : Tuple m.Val imports) (argsL argsR : Tuple m.Val caller.args) (store : σ)
    (agree : call.AgreesOnInputs demand importsL importsR argsL argsR) :
    ∃ observationL observationR,
      call.run actions (10 + more) unitId importsL argsL store = .ok observationL ∧
      call.run actions (10 + more) unitId importsR argsR store = .ok observationR ∧
      ObservationsAgree actions demand observationL observationR := by
  have same := primitiveInput_agrees call demand agree
  rw [settles call actions unitId more importsL argsL store, settles call actions unitId more importsR argsR store,
    ← same]
  cases tried : (actions.step call.opcode (primitiveInput call importsL argsL)).run store with
  | none =>
    refine ⟨_, _, rfl, rfl, .blocked ?_⟩
    intro value middle
    refine ⟨4, _, _, ?_, ?_, finish_agrees call demand agree value⟩
    · exact congrArg Config.result (resumes call actions importsL argsL value middle)
    · exact congrArg Config.result (resumes call actions importsR argsR value middle)
  | some result =>
    obtain ⟨value, middle⟩ := result
    exact ⟨_, _, rfl, rfl, .returned (finish_agrees call demand agree value)⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand.Proofs
