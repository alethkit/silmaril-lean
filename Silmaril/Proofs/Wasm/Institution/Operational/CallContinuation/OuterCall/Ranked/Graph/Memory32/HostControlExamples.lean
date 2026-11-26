module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Sequence.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.ControlExamples

open Execution.Runtime (Frame HostOutcome MemAddr MemInst ModuleInst Value)
open Wasm.V1.Execution

private abbrev i32 := Value.int .i32
private def slot : MemAddr := ⟨0⟩
private def hostType : Wasm.V1.FuncType := ⟨[.int .i32], [.int .i32]⟩
private def site : HostCall.V1.Site Nat := ⟨⟨0⟩, ⟨0⟩, hostType, 17⟩
private def mod : ModuleInst := { funcs := [site.address], memories := [slot] }
private def fn : Function :=
  ⟨⟨mod, ⟨0⟩, [.int .i32, .int .i32], [.int .i32], [.int .i32]⟩, 0, [i32 0], []⟩
private def root : HostEntry Nat := ⟨⟨0⟩, ⟨1⟩, fn, [.get ⟨1⟩], site⟩
private def seq : Sequence Nat := ⟨root, []⟩
private def graph : Program := ⟨[], none⟩
private def block : PathBlock := ⟨none, [.load 1]⟩
private def branch : PathBlock := ⟨some (.int .i32), [.ranked (.set ⟨2⟩)]⟩
private def choice : PathChoice := ⟨⟨0⟩, [.ranked (.numeric (.get ⟨1⟩))]⟩
private def branchNode : PathNode := ⟨branch, some choice⟩
private def path : List PathNode := [⟨block, none⟩, branchNode]
private def saved : List Value := [i32 0]
private def outerLabel : OpenLabel := ⟨saved, block⟩
private def innerLabel : OpenLabel := ⟨[], branch⟩
private def caller : Frame := ⟨[i32 44], { funcs := [root.address] }⟩
private def params (condition : BitVec 32) : List Value := [i32 condition, i32 9]
private def active (condition : BitVec 32) := fn.declaration.frame (params condition)
private def initial : MemInst := ⟨⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩, none⟩
private def written : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
private def base : Store Nat :=
  { funcs := [.host hostType 17, .wasm fn.declaration.type mod (seq.v1FuncAt path)], memories := [initial] }
private def live := storeWithBytes base slot initial initial.data
private def changed := storeWithBytes base slot initial written

private theorem guarded : PathNode.Allowed .fixed graph slot .ranked fn path := by
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · intro instr member
    obtain rfl := List.mem_singleton.mp member
    exact .source (.load 1 rfl)
  · intro test member
    cases member
  · intro instr member
    obtain rfl := List.mem_singleton.mp member
    exact .source (.set ⟨2⟩)
  · intro test used instr member
    have presented : some choice = some test := used
    have same : test = choice := (Option.some.inj presented).symm
    subst test
    obtain rfl := List.mem_singleton.mp member
    exact .get ⟨1⟩

private theorem checked (condition : BitVec 32) :
    seq.Checked .fixed graph slot .ranked base caller (params condition) path where
  resolved := rfl
  allocated := rfl
  parameters := rfl
  scalar := by decide
  slot := rfl
  linkedHosts := by
    intro found used
    have same : found = site := List.mem_singleton.mp used
    subst found
    exact ⟨rfl, rfl, by decide⟩
  typedBody := rfl
  guardedPath := guarded
  supportedTail := rfl
  linkedTail := by intro _ h; cases h

private theorem layout : Layout graph base slot initial where
  memory := rfl
  functions := by intro _ _ h; simp [graph, Program.lookup] at h

private inductive Outcome : HostOutcome Wasm.V1.Func Nat → Prop
  | ok : Outcome (.returned changed (.values [i32 7]))
  | trap : Outcome (.returned changed .trap)

private def host : HostSemantics Nat :=
  fun id store args answer => id = 17 ∧ store = live ∧ args = [i32 9] ∧ Outcome answer

private theorem contract : seq.Contract host .fixed slot initial base := by
  intro target used _ _ _ _ _ result outcome
  have same : target = site := List.mem_singleton.mp used
  subst target
  obtain ⟨_, store, _, returned⟩ := outcome
  rw [store]
  cases returned
  · exact ⟨rfl, initial.data, written, rfl, rfl, rfl⟩
  · exact ⟨trivial, initial.data, written, rfl, rfl, rfl⟩

private abbrev Phase := Sequence.Phase Nat
private abbrev Ready (phase : Phase) := seq.Ready .fixed graph slot .ranked initial phase path
private abbrev Runs (condition : BitVec 32) :=
  seq.Runs host .fixed graph slot base initial initial.data caller (params condition)
private abbrev cfg (condition : BitVec 32) := seq.render base slot initial initial.data caller (params condition)
private def source (condition : BitVec 32) : Config Nat :=
  ⟨live, caller, values (params condition) ++ [.source (.call ⟨0⟩)]⟩

private theorem correspondence (condition : BitVec 32) {dst : Config Nat} :
    Steps host (source condition) dst ↔ ∃ phase, Runs condition (.call path) phase ∧ Ready phase ∧ dst = cfg condition phase :=
  Sequence.v1_call_run_iff rfl (checked condition) layout trivial rfl contract

private theorem native {condition : BitVec 32} {phase : Phase}
    (run : Runs condition (.call path) phase) : Steps host (source condition) (cfg condition phase) := by
  have ready : Ready phase := by
    induction run with
    | refl => rfl
    | tail _ move ih => exact move.ready rfl (checked condition) layout rfl contract ih
  exact (correspondence condition).mpr ⟨phase, run, ready, rfl⟩

private theorem tested (condition : BitVec 32) : Runs condition (.call path)
    (.test [] branch choice [] condition [outerLabel]) := by
  have entered : Runs condition (.call path) (seq.beginPath initial.data saved [] path) :=
    (Relation.ReflTransGen.single .resolve).tail .enter
  have outer : Runs condition (.call path) (.path [] branchNode [] [outerLabel]) := entered.tail .openBlock
  exact outer.tail (.readCondition rfl)

private def pending : Phase := .pending initial.data [] [i32 9] site [] [innerLabel, outerLabel]
private theorem pendingRun : Runs 1 (.call path) pending := by
  have selected : Runs 1 (.call path) (.path [] ⟨branch, none⟩ [] [outerLabel]) :=
    (tested 1).tail (.choosePath (by decide))
  have entered : Runs 1 (.call path) (.computing initial.data [] root.operands site [] [innerLabel, outerLabel]) :=
    selected.tail .openBlock
  exact (entered.tail (.numeric (.get rfl))).tail (.hostResolve rfl)

private def framed (bytes : ByteArray) (f : Frame) (code : List Admin) : State :=
  ⟨bytes, caller, [.frame 1 f [.label 1 [] code]]⟩
private def load : Admin := .source ((Op.load 1).v1)
private def setLocal : Admin := .source (.localSet ⟨2⟩)
private def inOuter (code : List Admin) : List Admin := values saved ++ [.label 0 [] code, load]
private def payloadState (condition : BitVec 32) (bytes : ByteArray) (v : Value) : State :=
  framed bytes (active condition) (inOuter [.label 1 [] (values [v]), setLocal])

-- The dynamically reached pending host really sits beneath two distinct
-- labels, with its argument inside and the saved address outside.
example : Steps host (source 1)
    ⟨live, caller, [.frame 1 (active 1) [.label 1 [] (inOuter [.label 1 [] (values [i32 9] ++ [.invoke site.address]), setLocal])]]⟩ :=
  native pendingRun

private theorem finish (condition : BitVec 32) (bytes : ByteArray) (payload : Value) (word : BitVec 32)
    (read : MemoryQuery.EdgeAt bytes 1 (.load 0) (.value word)) :
    Memory32.Runs graph slot (payloadState condition bytes payload)
      ⟨bytes, caller, values [i32 word]⟩ := by
  let f := active condition
  let recorded : Frame := { f with locals := (params condition) ++ [payload] }
  have delivered : Memory32.Edge graph slot (payloadState condition bytes payload)
      (framed bytes f (inOuter (values [payload] ++ [setLocal]))) :=
    .frame (.label (.context (.label (.context (.pure (.labelDone 1 [] [payload])) [] [setLocal]) 0) saved [load]) 1) 1 caller
  have record : Memory32.Edge graph slot (framed bytes f (inOuter (values [payload] ++ [setLocal])))
      (framed bytes recorded (inOuter [])) :=
    .frame (.label (.context (.label (.set (old := i32 0) rfl) 0) saved [load]) 1) 1 caller
  have outerDone : Memory32.Edge graph slot (framed bytes recorded (inOuter []))
      (framed bytes recorded (values saved ++ [load])) :=
    .frame (.label (.context (.pure (.labelDone 0 [] [])) saved [load]) 1) 1 caller
  have readMemory : Memory32.Edge graph slot (framed bytes recorded (values saved ++ [load]))
      (framed bytes recorded (values [i32 word])) :=
    .frame (.label (.load (arg := immediate 1) rfl read) 1) 1 caller
  exact ((((Relation.ReflTransGen.single delivered).tail record).tail outerDone).tail readMemory
    |>.tail (.frame (.pure (.labelDone 1 [] [i32 word])) 1 caller))
    |>.tail (.pure (.frameDone 1 recorded [i32 word] rfl))

private theorem graphRuns {condition : BitVec 32} {before after : State}
    (pathRun : Runs condition (.call path) (.graph before)) (tail : Memory32.Runs graph slot before after) :
    Runs condition (.call path) (.graph after) := by
  induction tail with
  | refl => exact pathRun
  | tail _ move ih => exact ih.tail (.graph move)

-- Positive selection resumes through the scalar if label, consumes its
-- result in the void block's tail, and then reads the shared returned store.
example : Steps host (source 1) ⟨changed, caller, values [i32 0x11223344]⟩ := by
  have returned : host site.target live [i32 9] (.returned changed (.values [i32 7])) :=
    ⟨rfl, rfl, rfl, .ok⟩
  have resumed : Runs 1 (.call path) (.graph (payloadState 1 written (i32 7))) :=
    pendingRun.tail (.returned returned rfl)
  exact native (graphRuns resumed (finish 1 written (i32 7) 0x11223344 (MemoryQuery.fact_at (.load _ _ (by decide)))))

-- Zero selects the alternate block. Its result uses the same enclosing
-- labels and continuation, while its memory is the original allocation.
example : Steps host (source 0) ⟨live, caller, values [i32 0]⟩ := by
  have alternate : Runs 0 (.call path) (.graph
      (framed initial.data (active 0) (inOuter [.source (.block branch.result (v1Code choice.alternate)), setLocal]))) :=
    (tested 0).tail .chooseAlternate
  have enters : Memory32.Edge graph slot
      (framed initial.data (active 0) (inOuter [.source (.block branch.result (v1Code choice.alternate)), setLocal]))
      (framed initial.data (active 0) (inOuter [.label 1 [] [.source (.localGet ⟨1⟩)], setLocal])) :=
    .frame (.label (.context (.label (.context (.pure (.block branch.result (v1Code choice.alternate))) [] [setLocal]) 0)
      saved [load]) 1) 1 caller
  have reads : Memory32.Edge graph slot
      (framed initial.data (active 0) (inOuter [.label 1 [] [.source (.localGet ⟨1⟩)], setLocal]))
      (payloadState 0 initial.data (i32 9)) :=
    .frame (.label (.context (.label (.context (.label (.get rfl) 1) [] [setLocal]) 0) saved [load]) 1) 1 caller
  have finishes := finish 0 initial.data (i32 9) 0 (MemoryQuery.fact_at (.load _ _ (by decide)))
  exact native (graphRuns alternate ((finishes.head reads).head enters))

-- The host trap removes the inner label first. Its returned bytes survive
-- both enclosing tail discards, the outer label exits and frame unwind.
example : Steps host (source 1) ⟨changed, caller, [.trap]⟩ := by
  have trapped : host site.target live [i32 9] (.returned changed .trap) := ⟨rfl, rfl, rfl, .trap⟩
  have delivered : Runs 1 (.call path) (.trapped written [] [] [innerLabel, outerLabel]) :=
    pendingRun.tail (.returned trapped rfl)
  let f := active 1
  have close : Runs 1 (.call path) (.graph (framed written f (inOuter [.trap, setLocal]))) :=
    delivered.tail .closeTrap
  have discardInner : Memory32.Edge graph slot (framed written f (inOuter [.trap, setLocal]))
      (framed written f (inOuter [.trap])) :=
    .frame (.label (.context (.label (.pure (.trapTail setLocal [])) 0) saved [load]) 1) 1 caller
  have closeOuter : Memory32.Edge graph slot (framed written f (inOuter [.trap]))
      (framed written f (values saved ++ [.trap, load])) :=
    .frame (.label (.context (.pure (.labelTrap 0 [])) saved [load]) 1) 1 caller
  have discardOuter : Memory32.Edge graph slot (framed written f (values saved ++ [.trap, load]))
      (framed written f [.trap]) :=
    .frame (.label (.pure (.trapValues (i32 0) [] [load])) 1) 1 caller
  have cleanup : Memory32.Runs graph slot (framed written f (inOuter [.trap, setLocal]))
      ⟨written, caller, [.trap]⟩ :=
    (((Relation.ReflTransGen.single discardInner).tail closeOuter).tail discardOuter
      |>.tail (.frame (.pure (.labelTrap 1 [])) 1 caller))
      |>.tail (.pure (.frameTrap 1 f))
  exact native (graphRuns close cleanup)

-- Both arms must satisfy the declared scalar result.
example : seq.checkPath (Computed.Prefix.stackTypes fn.initial) fn.declaration.results fn.entryLabels
    [⟨block, none⟩, ⟨branch, some { choice with alternate := [] }⟩] = false := rfl

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.ControlExamples
