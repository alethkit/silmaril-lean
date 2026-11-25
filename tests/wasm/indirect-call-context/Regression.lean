import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (FuncAddr Frame Value)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context
open Silmaril.Wasm.Institution.Operational.CallContinuation
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def mixed : V1.FuncType := ⟨[.int .i64, .int .i32], [.int .i32, .int .i64]⟩
private def empty : V1.FuncType := ⟨[], []⟩
private def getLocal (i : LocalIdx) : Graph.Op := .numeric (.get i)

private def returning : Graph.Function :=
  ⟨⟨{ types := [mixed] }, ⟨0⟩, mixed.params, [.int .i32], mixed.results⟩, 0, [], [getLocal ⟨1⟩, getLocal ⟨0⟩]⟩

private def trapping : Graph.Function :=
  ⟨⟨{ types := [empty] }, ⟨0⟩, [], [], []⟩, 0, [], [.unreachable]⟩

private def selfDecl : Declaration := ⟨{ types := [empty], funcs := [⟨2⟩] }, ⟨0⟩, [], [], []⟩
private def self : CallTarget := ⟨⟨0⟩, ⟨2⟩, selfDecl⟩
private def recursive : Graph.Function := ⟨selfDecl, 0, [], [.call self]⟩

private def withReturn : V1.FuncType :=
  ⟨[.int .i32, .int .i64], [.int .i64, .int .i32, .int .i64, .int .i32]⟩
private def withVoid : V1.FuncType :=
  ⟨withReturn.params, [.int .i64, .int .i32]⟩
private def callerModule : Runtime.ModuleInst :=
  { tables := [⟨0⟩], types := [mixed, empty, withReturn, withVoid] }

private def owner : Graph.Function :=
  ⟨⟨callerModule, ⟨2⟩, withReturn.params, [], withReturn.results⟩, 0,
    [i64 7, i32 5, i64 42], [getLocal ⟨0⟩]⟩
private def ownerVoid : Graph.Function :=
  ⟨⟨callerModule, ⟨3⟩, withVoid.params, [], withVoid.results⟩, 0, [i64 7], [getLocal ⟨0⟩]⟩

private def functions : List Graph.Function := [returning, trapping, recursive, owner, ownerVoid]
private def program : Graph.Program := ⟨functions.map some⟩
private def table : Runtime.TableInst := ⟨[some ⟨0⟩, some ⟨1⟩, some ⟨2⟩], some 3⟩

-- The caller has no aliases to its targets, and its locals differ from the
-- callee's arguments and default local. The return exposes local.get 0.
private def caller : Frame := ⟨[i32 91, i64 73], callerModule⟩
private def saved : List Value := [i64 7]
private def coreRest : List Core.Admin := [.plain (.localGet ⟨0⟩), .plain .nop]
private def limeRest : List Lime1.Execution.Admin := [.source (.localGet ⟨0⟩), .source .nop]
private def returnCall : Invocation :=
  ⟨⟨table, ⟨0⟩, mixed⟩, caller, 0, saved, [i64 42, i32 5], ⟨0⟩, returning⟩
private def trapCall : Invocation :=
  ⟨⟨table, ⟨1⟩, empty⟩, caller, 1, saved, [], ⟨1⟩, trapping⟩
private def recursiveCall : Invocation :=
  ⟨⟨table, ⟨1⟩, empty⟩, caller, 2, saved, [], ⟨2⟩, recursive⟩

private theorem returnChecked : returnCall.Checked program := ⟨rfl, rfl, rfl, rfl, rfl⟩
private theorem trapChecked : trapCall.Checked program := ⟨rfl, rfl, rfl, rfl, rfl⟩
private theorem recursiveChecked : recursiveCall.Checked program := ⟨rfl, rfl, rfl, rfl, rfl⟩
example : caller.module.funcs = [] := rfl

private def coreStore : Core.Store Unit :=
  { funcs := functions.map Graph.Function.coreInstance, tables := [table.toCore] }
private def limeStore : Lime1.Execution.Store Unit :=
  { funcs := functions.map fun fn => .wasm fn.declaration.type fn.declaration.module fn.limeFunc
    tables := [table] }

private theorem coreAllocated : program.CoreAllocated coreStore := by
  intro addr fn found
  cases slot : functions[addr.value]? <;>
    simp_all [Graph.Program.lookup, program, coreStore, List.getElem?_map]

private theorem limeAllocated : program.LimeAllocated limeStore := by
  intro addr fn found
  cases slot : functions[addr.value]? <;>
    simp_all [Graph.Program.lookup, program, limeStore, List.getElem?_map]

private abbrev spec := Numerics.Profile.spec
private abbrev returnPhase : Graph.Phase := .done (.values [i32 5, i64 42])

example : (returnCall.corePrefix coreStore coreRest).length = 5 := rfl
example : (returnCall.limePrefix limeStore limeRest).length = 3 := rfl
example := core_prefix_exact (P := spec) (s := coreStore) (rest := coreRest) returnChecked coreAllocated (addr := 0) rfl
example := lime_prefix_exact (s := limeStore) (rest := limeRest) returnChecked limeAllocated rfl

private theorem returnPath : program.FrameRuns ⟨0⟩ returnCall.entered returnPhase := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) returnChecked.found).mpr
  have first := Relation.ReflTransGen.single (edge (.numeric (locals := [i64 42, i32 5, i32 0])
    (rest := [getLocal ⟨0⟩]) (.get (stack := []) (i := ⟨1⟩) (v := i32 5) rfl)))
  have second := first.tail (edge (.numeric (rest := []) (.get (stack := [i32 5]) (i := ⟨0⟩) (v := i64 42) rfl)))
  exact (second.tail (edge (.leaveValues [i64 42, i32 5, i32 0] [i32 5, i64 42]))).tail
    (edge (.leaveFrame _ (.values [i32 5, i64 42]) rfl))

private theorem trapPath : program.FrameRuns ⟨1⟩ trapCall.entered (.done .trap) := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) trapChecked.found).mpr
  exact ((Relation.ReflTransGen.single (edge (.unreachable [] [] []))).tail (edge (.leaveTrap []))).tail
    (edge (.leaveFrame [] .trap trivial))

private theorem admitted {call : Invocation} (checked : call.Checked program) {phase : Graph.Phase}
    (path : program.FrameRuns call.address call.entered phase) : Graph.Admitted program call.callee phase :=
  program.frame_admitted_run checked.graph checked.found
    (entered_admitted checked) path

private theorem coreRun {call : Invocation} (checked : call.Checked program)
    (allocatedTable : coreStore.table? call.caller.toCore tableIndex = some (0, call.site.table.toCore))
    {phase : Graph.Phase}
    (path : program.FrameRuns call.address call.entered phase) :
    call.CoreRun spec coreStore coreRest (call.coreCallee coreStore coreRest phase) :=
  (core_run_iff checked coreAllocated allocatedTable).mpr (.inr (.inl ⟨phase, path, admitted checked path, rfl⟩))

private theorem limeRun {call : Invocation} (checked : call.Checked program)
    (allocatedTable : Lime1.Execution.frameTable limeStore call.caller = some call.site.table)
    {phase : Graph.Phase}
    (path : program.FrameRuns call.address call.entered phase) :
    call.LimeRun limeStore limeRest (call.limeCallee limeStore limeRest phase) :=
  (lime_run_iff checked limeAllocated allocatedTable).mpr (.inr (.inl ⟨phase, path, admitted checked path, rfl⟩))

private def coreResume : Core.Config Unit :=
  ⟨coreStore, caller.toCore, coreValues [i64 7, i32 5, i64 42] ++ coreRest⟩
private def limeResume : Lime1.Execution.Config Unit :=
  ⟨limeStore, caller, Lime1.Execution.values [i64 7, i32 5, i64 42] ++ limeRest⟩

example : Core.Steps spec noHost
    (coreConfig coreStore caller returnCall.site 0 (saved ++ returnCall.args) coreRest .start) coreResume :=
  core_steps_of_run (coreRun returnChecked rfl returnPath)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeSource limeStore caller returnCall.site 0 (saved ++ returnCall.args) limeRest) limeResume :=
  lime_steps_of_run (limeRun returnChecked rfl returnPath)

-- The pending local.get observes the restored caller's local.
example : Core.Step spec noHost coreResume
    ⟨coreStore, caller.toCore, coreValues [i64 7, i32 5, i64 42, i32 91] ++ [.plain .nop]⟩ :=
  (Prefix.core_step_iff (f := caller) (op := .get ⟨0⟩) (stack := [i64 7, i32 5, i64 42])
    (tail := [.plain .nop])).mpr ⟨_, .get (i := ⟨0⟩) rfl, rfl⟩

example : Lime1.Execution.Step CallFrame.limeNoHost limeResume
    ⟨limeStore, caller, Lime1.Execution.values [i64 7, i32 5, i64 42, i32 91] ++ [.source .nop]⟩ :=
  (Prefix.lime_step_iff (f := caller) (op := .get ⟨0⟩) (stack := [i64 7, i32 5, i64 42])
    (tail := [.source .nop])).mpr ⟨_, .get (i := ⟨0⟩) rfl, rfl⟩

-- The native caller can resume, and this step is outside the fenced frame run.
example (next : Core.Config Unit) : ¬ returnCall.coreFrameStep spec coreRest coreResume next :=
  core_handoff_stops (call := returnCall) (.values [i32 5, i64 42]) next

example (next : Lime1.Execution.Config Unit) : ¬ returnCall.limeFrameStep limeRest limeResume next :=
  lime_handoff_stops (call := returnCall) (.values [i32 5, i64 42]) next

private theorem cleanup {A : Type} (rest : List A) (pending : rest ≠ []) :
    Relation.ReflTransGen (fun (a b : List Value × List A) => Prefix.Discard a.1 a.2 b.1 b.2)
      (saved, rest) ([], []) := by
  have dropSaved : Prefix.Discard saved rest [] rest := .cut [] saved [] rest (.inl (by simp [saved]))
  have dropRest : Prefix.Discard ([] : List Value) rest [] [] := by
    simpa only [List.append_nil] using (Prefix.Discard.cut [] [] rest [] (.inr pending))
  exact (Relation.ReflTransGen.single (b := ([], rest)) dropSaved).tail dropRest

example : Core.Steps spec noHost (coreConfig coreStore caller trapCall.site 1 saved coreRest .start)
    ⟨coreStore, caller.toCore, [.trap]⟩ :=
  core_steps_of_run
    ((core_run_iff trapChecked coreAllocated (addr := 0) rfl).mpr (.inr (.inr ⟨trapPath, [], [], cleanup coreRest (by decide), rfl⟩)))

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore caller trapCall.site 1 saved limeRest)
    ⟨limeStore, caller, [.trap]⟩ :=
  lime_steps_of_run
    ((lime_run_iff trapChecked limeAllocated rfl).mpr (.inr (.inr ⟨trapPath, [], [], cleanup limeRest (by decide), rfl⟩)))

-- Every finite depth is observable after the single indirect root lookup.
-- The recursive body only uses its own checked direct target.
private def deep : Nat → Graph.Phase
  | 0 => recursiveCall.entered
  | n + 1 => .label [] (.active [] self (deep n) [])

private theorem deepActive (n : Nat) : (deep n).Active := by cases n <;> trivial

private theorem selfUsed : self ∈ recursive.targets := by
  simp [recursive, Graph.Function.targets, Graph.codeTargets, Graph.Op.targets]

private theorem deeper (n : Nat) : program.FrameRuns ⟨2⟩ (deep n) (deep (n + 1)) := by
  induction n with
  | zero =>
    have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) recursiveChecked.found).mpr
    exact (Relation.ReflTransGen.single (edge (.dispatch [] [] [] self [] selfUsed rfl))).tail
      (edge (.child [] [] self [] (a := .invoke []) (b := deep 0) selfUsed trivial (edge (.enter [] rfl))))
  | succ n ih =>
    exact program.frame_lift_child recursiveChecked.found selfUsed (deepActive n)
      (locals := []) (saved := []) (rest := []) ih

private theorem recursivePrefix (n : Nat) : program.FrameRuns ⟨2⟩ recursiveCall.entered (deep n) := by
  induction n with
  | zero => exact .refl
  | succ n ih => exact ih.trans (deeper n)

example (n : Nat) : Core.Steps spec noHost (coreConfig coreStore caller recursiveCall.site 2 saved coreRest .start)
    (recursiveCall.coreCallee coreStore coreRest (deep n)) :=
  core_steps_of_run (coreRun recursiveChecked rfl (recursivePrefix n))

example (n : Nat) : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeSource limeStore caller recursiveCall.site 2 saved limeRest) (recursiveCall.limeCallee limeStore limeRest (deep n)) :=
  lime_steps_of_run (limeRun recursiveChecked rfl (recursivePrefix n))

example (n : Nat) : ((deep n).frames ⟨2⟩).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((deep n).frames ⟨2⟩).length + 1 = n + 1 + 1
    rw [ih]

open Context.Resume in
private def returnedCont : Continuation := ⟨⟨3⟩, owner, [getLocal ⟨0⟩], []⟩

open Context.Resume in
private def voidCont : Continuation := ⟨⟨4⟩, ownerVoid, [getLocal ⟨0⟩], []⟩

private theorem returnedContChecked : returnedCont.Checked program caller saved mixed.results :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
private theorem voidContChecked : voidCont.Checked program caller saved empty.results :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private def outer : Frame := ⟨[i64 300], {}⟩
private def finalResults : List Value := [i64 7, i32 5, i64 42, i32 91]

example : (returnedCont.corePrefix returnCall coreStore outer).length = 5 := rfl
example : (returnedCont.limePrefix returnCall limeStore outer).length = 3 := rfl

example : ¬ returnedCont.Checked program caller saved empty.results := by
  intro bad
  have rejected : Graph.checkCode owner.targets owner.localTypes owner.declaration.results
      owner.declaration.results [] (Prefix.stackTypes saved) returnedCont.code .exit callerModule.types = false := rfl
  exact Bool.noConfusion (rejected.symm.trans bad.tail_typed)

-- Both raw finite relations retain the native states before frame entry.
example : Core.Steps spec noHost
    (returnedCont.coreSiteWrap outer
      (coreConfig coreStore caller returnCall.site 0 (saved ++ returnCall.args) (returnedCont.code.map Graph.coreEmit) .start))
    (returnedCont.coreSiteWrap outer
      (coreConfig coreStore caller returnCall.site 0 (saved ++ returnCall.args)
        (returnedCont.code.map Graph.coreEmit) (.cast (some ⟨0⟩)))) :=
  (Resume.core_run_iff returnChecked coreAllocated returnedContChecked (addr := 0) rfl).mpr
    (.inl (by simp [Resume.Continuation.corePrefix, Invocation.corePrefix, Outcome.coreTrace, returnCall]))

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (returnedCont.limeSiteWrap outer
      (limeSource limeStore caller returnCall.site 0 (saved ++ returnCall.args) (returnedCont.code.map Graph.limeEmit)))
    (returnedCont.limeSiteWrap outer
      (limeResolved limeStore caller (saved ++ returnCall.args) (returnedCont.code.map Graph.limeEmit) (.resolved ⟨0⟩))) :=
  (Resume.lime_run_iff returnChecked limeAllocated returnedContChecked rfl).mpr
    (.inl (by simp [Resume.Continuation.limePrefix, Invocation.limePrefix, returnCall]))

private theorem restoredPath : Resume.Runs program returnCall returnedCont (.callee returnCall.entered)
    (.caller (.done (.values finalResults))) := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) returnedContChecked.found).mpr
  have joined := Resume.of_callee_run (cont := returnedCont) returnChecked returnPath
  have resumed := joined.tail (.resume (edge (.numeric (locals := caller.locals)
    (rest := []) (.get (stack := [i64 7, i32 5, i64 42]) (i := ⟨0⟩) (v := i32 91) rfl))))
  exact (resumed.tail (.caller (edge (.leaveValues caller.locals finalResults)))).tail
    (.caller (edge (.leaveFrame caller.locals (.values finalResults) rfl)))

example : Core.Steps spec noHost
    (returnedCont.coreSiteWrap outer
      (coreConfig coreStore caller returnCall.site 0 (saved ++ returnCall.args) (returnedCont.code.map Graph.coreEmit) .start))
    ⟨coreStore, outer.toCore, coreValues finalResults⟩ :=
  (Resume.core_run_iff returnChecked coreAllocated returnedContChecked (addr := 0) rfl).mpr
    (.inr ⟨_, restoredPath, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (returnedCont.limeSiteWrap outer
      (limeSource limeStore caller returnCall.site 0 (saved ++ returnCall.args) (returnedCont.code.map Graph.limeEmit)))
    ⟨limeStore, outer, Lime1.Execution.values finalResults⟩ :=
  (Resume.lime_run_iff returnChecked limeAllocated returnedContChecked rfl).mpr (.inr ⟨_, restoredPath, rfl⟩)

-- A callee trap hands off to the caller's discard phase instead of running local.get.
private theorem unwoundPath : Resume.Runs program trapCall voidCont (.callee trapCall.entered)
    (.caller (.done .trap)) := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) voidContChecked.found).mpr
  have joined := Resume.of_callee_run (cont := voidCont) trapChecked trapPath
  have cut : Prefix.Discard saved voidCont.code [] [] := by
    simpa only [List.nil_append, List.append_nil] using
      (Prefix.Discard.cut [] saved voidCont.code [] (.inl (by simp [saved])))
  exact ((joined.tail (.resume (edge (.discard (locals := caller.locals) cut)))).tail
    (.caller (edge (.leaveTrap caller.locals)))).tail (.caller (edge (.leaveFrame caller.locals .trap trivial)))

example : Core.Steps spec noHost
    (voidCont.coreWrap outer (coreConfig coreStore caller trapCall.site 1 saved (voidCont.code.map Graph.coreEmit) .start))
    ⟨coreStore, outer.toCore, [.trap]⟩ :=
  (Resume.core_run_iff trapChecked coreAllocated voidContChecked (addr := 0) rfl).mpr
    (.inr ⟨_, unwoundPath, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (voidCont.limeWrap outer (limeSource limeStore caller trapCall.site 1 saved (voidCont.code.map Graph.limeEmit)))
    ⟨limeStore, outer, [.trap]⟩ :=
  (Resume.lime_run_iff trapChecked limeAllocated voidContChecked rfl).mpr (.inr ⟨_, unwoundPath, rfl⟩)

-- A bounds trap is admitted resolution. Invalid type indices and dangling
-- table entries are rejected before the contextual theorem is applicable.
example : trapCall.site.resolve program (-1) = some .bounds := rfl
example : ({ trapCall.site with typeIndex := ⟨99⟩ }).check program caller = false := rfl
example : ({ trapCall.site with table := ⟨[some ⟨99⟩], none⟩ }).check program caller = false := rfl

private def coreBounds (phase : Phase) : Core.Config Unit :=
  voidCont.coreWrap outer (coreConfig coreStore caller trapCall.site (-1) saved (voidCont.code.map Graph.coreEmit) phase)

private theorem coreBoundsPath : Core.Steps spec noHost (coreBounds .start) (coreBounds .boundsTrap) := by
  have chain := Resume.core_resolution_prefix_exact (P := spec) (s := coreStore) (cont := voidCont)
    (outer := outer) (stack := saved) (selector := -1) (out := .bounds) trapChecked.site coreAllocated (addr := 0) rfl rfl
  obtain ⟨start, more⟩ := List.isChain_cons_cons.mp chain
  obtain ⟨lookup, _⟩ := List.isChain_cons_cons.mp more
  exact (Relation.ReflTransGen.single ((start _).mpr rfl)).tail ((lookup _).mpr rfl)

example : Core.Steps spec noHost (coreBounds .start) ⟨coreStore, outer.toCore, [.trap]⟩ := by
  have discard : Core.Step spec noHost (coreBounds .boundsTrap) (voidCont.coreWrap outer ⟨coreStore, caller.toCore, [.trap]⟩) :=
    .ctxtFrame (.ctxtLabel (.trapInstrs (vs := saved.map Value.toCore) (.inl (by simp [saved]))))
  exact ((coreBoundsPath.tail discard).tail (.ctxtFrame .trapLabel)).tail .trapFrame

private theorem limeBounds :
    Lime1.Execution.Step CallFrame.limeNoHost
      (voidCont.limeWrap outer (limeSource limeStore caller trapCall.site (-1) saved (voidCont.code.map Graph.limeEmit)))
      (voidCont.limeWrap outer (limeResolved limeStore caller saved (voidCont.code.map Graph.limeEmit) .bounds)) :=
  (Resume.lime_resolution_step_iff (selector := -1) trapChecked.site limeAllocated rfl rfl).mpr rfl

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (voidCont.limeWrap outer (limeSource limeStore caller trapCall.site (-1) saved (voidCont.code.map Graph.limeEmit)))
    ⟨limeStore, outer, [.trap]⟩ := by
  have discard : Lime1.Execution.Step CallFrame.limeNoHost
      (voidCont.limeWrap outer (limeResolved limeStore caller saved (voidCont.code.map Graph.limeEmit) .bounds))
      (voidCont.limeWrap outer ⟨limeStore, caller, [.trap]⟩) :=
    .frame (.label (.pure limeStore caller (.trapValues (i64 7) [] _)) _ []) _ outer
  exact (((Relation.ReflTransGen.single limeBounds).tail discard).tail
    (.frame (.pure limeStore caller (.labelTrap _ [])) _ outer)).tail
    (.pure limeStore outer (.frameTrap _ caller))

example (n : Nat) : Core.Steps spec noHost
    (voidCont.coreWrap outer
      (coreConfig coreStore caller recursiveCall.site 2 saved (voidCont.code.map Graph.coreEmit) .start))
    (voidCont.coreConfig recursiveCall coreStore outer (.callee (deep n))) :=
  (Resume.core_run_iff recursiveChecked coreAllocated voidContChecked (addr := 0) rfl).mpr
    (.inr ⟨_, Resume.of_callee_run recursiveChecked (recursivePrefix n), rfl⟩)

example (n : Nat) : Lime1.Execution.Steps CallFrame.limeNoHost
    (voidCont.limeWrap outer
      (limeSource limeStore caller recursiveCall.site 2 saved (voidCont.code.map Graph.limeEmit)))
    (voidCont.limeConfig recursiveCall limeStore outer (.callee (deep n))) :=
  (Resume.lime_run_iff recursiveChecked limeAllocated voidContChecked rfl).mpr
    (.inr ⟨_, Resume.of_callee_run recursiveChecked (recursivePrefix n), rfl⟩)
