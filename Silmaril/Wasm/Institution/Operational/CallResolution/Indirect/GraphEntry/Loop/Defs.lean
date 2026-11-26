module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop

open Execution
open Execution.Runtime (Frame FuncAddr Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

/-- One parameterless loop around a computed site. Each trip tests the old
restart local after replacing it with the value of another i32 local.
A zero restart test falls through to a separate choice of the site arm
or the empty arm. -/
structure Entry where
  address : FuncAddr
  owner : Graph.Function
  result : Option NumType
  restart : LocalIdx
  nextRestart : LocalIdx
  branchTypes : List NumType
  choose : LocalIdx
  op : Source.Op
  before : List Prefix.Op
  insideTail : List Graph.Op
  tail : List Graph.Op

def Entry.cont (entry : Entry) : Context.Resume.Continuation :=
  ⟨entry.address, entry.owner, entry.tail, []⟩

def Entry.siteBody (entry : Entry) : Source.Body :=
  .indirect entry.before entry.op entry.insideTail

def Entry.prefix (entry : Entry) : List Graph.Op :=
  [.numeric (.get entry.restart), .numeric (.get entry.nextRestart), .set entry.restart,
    .brIf ⟨0⟩ entry.branchTypes, .numeric (.get entry.choose)]

def Entry.iteration {I : Type} (entry : Entry) (codec : Graph.CodeSyntax I) (indirect : Source.Op → I) : List I :=
  Graph.Op.emitList codec entry.prefix ++ [codec.if_ entry.result (entry.siteBody.emit codec indirect) []]

def Entry.check (entry : Entry) (program : Graph.Program) (tables : Source.Tables) : Bool :=
  let fn := entry.owner
  let kind := Graph.LabelKind.loop entry.result []
  program.checkDirect &&
    [entry.restart, entry.nextRestart, entry.choose].all
      (fun i => decide (fn.localTypes[i.toNat]? = some (.int .i32))) &&
    entry.result.isNone &&
    Graph.checkCode fn.targets fn.localTypes fn.declaration.results entry.result.toList
      [fn.declaration.results] [] (entry.prefix ++ [.if_ entry.result [.unreachable] []])
      kind fn.declaration.module.types &&
    entry.siteBody.checkRegion program tables fn entry.result.toList [[], fn.declaration.results] [] &&
    Graph.checkCode fn.targets fn.localTypes fn.declaration.results fn.declaration.results []
      (entry.result.toList.reverse ++ Prefix.stackTypes fn.initial) entry.tail .exit fn.declaration.module.types

structure Entry.Checked (entry : Entry) (program : Graph.Program) (tables : Source.Tables)
    (outer : Frame) (index : FuncIdx) (args : List Value) : Prop where
  source : entry.check program tables = true
  found : program.lookup entry.address = some entry.owner
  resolves : outer.module.funcs[index.toNat]? = some entry.address
  typed : args.map Value.type = entry.owner.declaration.params

inductive Phase where
  | enter
  | readRestart
  | readNext (old : BitVec 32)
  | writeRestart (old next : BitVec 32)
  | testRestart (old : BitVec 32)
  | branch
  | readChoice
  | testChoice (value : BitVec 32)
  | arm (site : Bool)
  | emptyArm
  | exitLoop
  | site
  | caller

def Phase.Pending : Phase → Prop
  | .site | .caller => False
  | _ => True

structure State where
  locals : List Value
  phase : Phase

def Entry.initial (entry : Entry) (args : List Value) : State :=
  ⟨(entry.owner.declaration.frame args).locals, .enter⟩

def Entry.callerPhase (entry : Entry) (locals : List Value) : Graph.Phase :=
  .label locals (.running entry.owner.initial entry.tail)

def Entry.frame (entry : Entry) (locals : List Value) : Frame :=
  Graph.currentFrame entry.owner.declaration locals

def Entry.Typed (entry : Entry) (state : State) : Prop :=
  state.locals.map Value.type = entry.owner.localTypes

/-- Restart reinstalls the source loop, retaining the updated locals. An
empty alternate instead exits to the saved stack and the function tail.
The site checkpoint has an open operand prefix and an entered arm label. -/
inductive Edge (entry : Entry) : State → State → Prop where
  | enter {locals} : Edge entry ⟨locals, .enter⟩ ⟨locals, .readRestart⟩
  | readRestart {locals old} (found : locals[entry.restart.toNat]? = some (.int .i32 old)) :
      Edge entry ⟨locals, .readRestart⟩ ⟨locals, .readNext old⟩
  | readNext {locals old next} (found : locals[entry.nextRestart.toNat]? = some (.int .i32 next)) :
      Edge entry ⟨locals, .readNext old⟩ ⟨locals, .writeRestart old next⟩
  | writeRestart {locals nextLocals old next}
      (write : Locals.Edge ⟨locals, [.value (.int .i32 next), .set entry.restart]⟩ ⟨nextLocals, []⟩) :
      Edge entry ⟨locals, .writeRestart old next⟩ ⟨nextLocals, .testRestart old⟩
  | testRestart {locals old} :
      Edge entry ⟨locals, .testRestart old⟩ ⟨locals, if old = 0 then .readChoice else .branch⟩
  | restart {locals} : Edge entry ⟨locals, .branch⟩ ⟨locals, .enter⟩
  | readChoice {locals value} (found : locals[entry.choose.toNat]? = some (.int .i32 value)) :
      Edge entry ⟨locals, .readChoice⟩ ⟨locals, .testChoice value⟩
  | testChoice {locals value} :
      Edge entry ⟨locals, .testChoice value⟩ ⟨locals, .arm (decide (value ≠ 0))⟩
  | enterSite {locals} : Edge entry ⟨locals, .arm true⟩ ⟨locals, .site⟩
  | enterEmpty {locals} : Edge entry ⟨locals, .arm false⟩ ⟨locals, .emptyArm⟩
  | leaveEmpty {locals} : Edge entry ⟨locals, .emptyArm⟩ ⟨locals, .exitLoop⟩
  | leaveLoop {locals} : Edge entry ⟨locals, .exitLoop⟩ ⟨locals, .caller⟩

abbrev Runs (entry : Entry) := Relation.ReflTransGen (Edge entry)

def Entry.coreLoop (entry : Entry) : Instr :=
  .loop (Blocks.coreType entry.result) (entry.iteration Graph.coreCodeSyntax Source.Op.coreInstr)

def Entry.limeLoop (entry : Entry) : Wasm.Lime1.Instr :=
  .loop (Blocks.limeType entry.result) (entry.iteration Graph.limeCodeSyntax Source.Op.limeInstr)

def Entry.coreFunc (entry : Entry) : Wasm.Func :=
  let body := entry.owner.initial.map Graph.coreCodeSyntax.ops.value ++
    entry.coreLoop :: Graph.Op.emitList Graph.coreCodeSyntax entry.tail
  { entry.owner.coreFunc with body := body }

def Entry.limeFunc (entry : Entry) : Wasm.Lime1.Func :=
  let body := entry.owner.initial.map Graph.limeCodeSyntax.ops.value ++
    entry.limeLoop :: Graph.Op.emitList Graph.limeCodeSyntax entry.tail
  { entry.owner.limeFunc with body := body }

def Entry.coreInstance {H : Type} (entry : Entry) : Core.FuncInst H :=
  ⟨entry.owner.declaration.type.toDefType, entry.owner.declaration.module.toCore, .wasm entry.coreFunc⟩

def Entry.limeInstance {H : Type} (entry : Entry) : Runtime.FuncInst Wasm.Lime1.Func H :=
  .wasm entry.owner.declaration.type entry.owner.declaration.module entry.limeFunc

/-- The two administrative label operations differ only in their native codec.
The loop continuation is the actual source loop, including the site arm. -/
def Entry.iterationCode {I A : Type} (entry : Entry) (codec : Graph.CodeSyntax I) (ops : Graph.Syntax A)
    (indirect : Source.Op → I) (expr : List I → List A) (label : Nat → List I → List A → A) :
    Phase → List A
  | .readRestart => expr (entry.iteration codec indirect)
  | .readNext old => ops.values [.int .i32 old] ++
      expr ((entry.iteration codec indirect).drop 1)
  | .writeRestart old next => ops.values [.int .i32 old, .int .i32 next] ++
      expr ((entry.iteration codec indirect).drop 2)
  | .testRestart old => ops.values [.int .i32 old] ++ expr ((entry.iteration codec indirect).drop 3)
  | .branch => ops.emit (.br ⟨0⟩ entry.branchTypes) :: expr ((entry.iteration codec indirect).drop 4)
  | .readChoice => expr ((entry.iteration codec indirect).drop 4)
  | .testChoice value => ops.values [.int .i32 value] ++ expr ((entry.iteration codec indirect).drop 5)
  | .arm site => expr [codec.block entry.result (if site then entry.siteBody.emit codec indirect else [])]
  | .emptyArm => [label entry.result.toList.length [] []]
  | .site => [label entry.result.toList.length [] (expr (entry.siteBody.emit codec indirect))]
  | .exitLoop | .enter | .caller => []

def Entry.coreLoopWrap {H : Type} (entry : Entry) (outer : Frame) (inside : Core.Config H) : Core.Config H :=
  entry.cont.coreWrap outer
    ⟨inside.store, inside.frame, coreValues entry.owner.initial ++ .label 0 [entry.coreLoop] inside.code ::
      entry.tail.map Graph.coreEmit⟩

open Wasm.Lime1.Execution in
def Entry.limeLoopWrap {H : Type} (entry : Entry) (outer : Frame) (inside : Config H) : Config H :=
  entry.cont.limeWrap outer
    ⟨inside.store, inside.frame, values entry.owner.initial ++ .label 0 [entry.limeLoop] inside.code ::
      entry.tail.map Graph.limeEmit⟩

def Entry.coreConfig {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (state : State) : Core.Config H :=
  match state.phase with
  | .enter => entry.cont.coreWrap outer ⟨s, (entry.frame state.locals).toCore,
      coreValues entry.owner.initial ++ .plain entry.coreLoop :: entry.tail.map Graph.coreEmit⟩
  | .caller => Graph.coreConfig s outer entry.cont.target (entry.callerPhase state.locals)
  | phase => entry.coreLoopWrap outer ⟨s, (entry.frame state.locals).toCore,
      entry.iterationCode Graph.coreCodeSyntax Graph.coreAdmin Source.Op.coreInstr Core.expression .label phase⟩

open Wasm.Lime1.Execution in
def Entry.limeConfig {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (state : State) : Config H :=
  match state.phase with
  | .enter => entry.cont.limeWrap outer ⟨s, entry.frame state.locals,
      values entry.owner.initial ++ .source entry.limeLoop :: entry.tail.map Graph.limeEmit⟩
  | .caller => Graph.limeConfig s outer entry.cont.target (entry.callerPhase state.locals)
  | phase => entry.limeLoopWrap outer ⟨s, entry.frame state.locals,
      entry.iterationCode Graph.limeCodeSyntax Graph.limeAdmin Source.Op.limeInstr expression .label phase⟩

/-- The selected conditional arm is a block nested within the live loop. -/
def Entry.armScope (entry : Entry) : Blocks.Context.Scope Graph.Op :=
  ⟨entry.result.toList.length, [], []⟩

def Entry.coreArmWrap {H : Type} (entry : Entry) (outer : Frame) (inside : Core.Config H) : Core.Config H :=
  entry.coreLoopWrap outer { inside with code := [.label entry.result.toList.length [] inside.code] }

def Entry.coreSiteCode (entry : Entry) (rest : List Prefix.Op) : List Core.Admin :=
  rest.map (Prefix.emit coreSyntax) ++ .plain entry.op.coreInstr :: entry.insideTail.map Graph.coreEmit

def Entry.coreOperands {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame)
    (locals : List Value) (state : OperandState) : Core.Config H :=
  entry.coreArmWrap outer ⟨s, (entry.frame locals).toCore, coreValues state.1 ++ entry.coreSiteCode state.2⟩

def Entry.coreOperandResult {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame)
    (locals : List Value) : OperandResult → Core.Config H
  | .values stack => entry.coreOperands s outer locals (stack, [])
  | .trap saved rest =>
      entry.coreArmWrap outer ⟨s, (entry.frame locals).toCore, coreValues saved ++ .trap :: entry.coreSiteCode rest⟩

open Wasm.Lime1.Execution in
def Entry.limeArmWrap {H : Type} (entry : Entry) (outer : Frame) (inside : Config H) : Config H :=
  entry.limeLoopWrap outer { inside with code := [.label entry.result.toList.length [] inside.code] }

open Wasm.Lime1.Execution in
def Entry.limeSiteCode (entry : Entry) (rest : List Prefix.Op) : List Admin :=
  rest.map (Prefix.emit limeSyntax) ++ .source entry.op.limeInstr :: entry.insideTail.map Graph.limeEmit

open Wasm.Lime1.Execution in
def Entry.limeOperands {H : Type} (entry : Entry) (s : Store H) (outer : Frame)
    (locals : List Value) (state : OperandState) : Config H :=
  entry.limeArmWrap outer ⟨s, entry.frame locals, values state.1 ++ entry.limeSiteCode state.2⟩

open Wasm.Lime1.Execution in
def Entry.limeOperandResult {H : Type} (entry : Entry) (s : Store H) (outer : Frame)
    (locals : List Value) : OperandResult → Config H
  | .values stack => entry.limeOperands s outer locals (stack, [])
  | .trap saved rest =>
      entry.limeArmWrap outer ⟨s, entry.frame locals, values saved ++ .trap :: entry.limeSiteCode rest⟩

def Entry.coreLookup {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame)
    (active : Source.Activation) (phase : Indirect.Phase) : Core.Config H :=
  entry.coreLoopWrap outer (active.coreConfig s [entry.armScope] entry.insideTail phase)

open Wasm.Lime1.Execution in
def Entry.limeLookup {H : Type} (entry : Entry) (s : Store H) (outer : Frame)
    (active : Source.Activation) : Config H :=
  entry.limeLoopWrap outer (active.limeSource s [entry.armScope] entry.insideTail)

open Wasm.Lime1.Execution in
def Entry.limeLookupResult {H : Type} (entry : Entry) (s : Store H) (outer : Frame)
    (active : Source.Activation) (out : Outcome) : Config H :=
  entry.limeLoopWrap outer (active.limeResolved s [entry.armScope] entry.insideTail out)

/-- Every finite native endpoint lies within the recurrent path or extends a
reached site checkpoint. The caller branch runs the ordinary checked tail. -/
def Observation {C : Type} (entry : Entry) (args : List Value) (render : State → C)
    (caller : List Value → C → Prop) (native : C → C → Prop) (dst : C) : Prop :=
  (∃ state, Runs entry (entry.initial args) state ∧ dst = render state) ∨
  (∃ locals, Runs entry (entry.initial args) ⟨locals, .caller⟩ ∧ caller locals dst) ∨
  (∃ locals, Runs entry (entry.initial args) ⟨locals, .site⟩ ∧
    Relation.ReflTransGen native (render ⟨locals, .site⟩) dst)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop
