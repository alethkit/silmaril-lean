import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame Value)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallResolution
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def sigA : V1.FuncType := ⟨[.int .i64], [.int .i64]⟩
private def sigB : V1.FuncType := ⟨[], [.int .i32]⟩
private def callerAType : V1.FuncType := ⟨[.int .i64, .int .i32, .int .i32], [.int .i32, .int .i64, .int .i32]⟩
private def callerBType : V1.FuncType := ⟨[.int .i32, .int .i64], [.int .i64, .int .i32, .int .i64]⟩
private def moduleA : Runtime.ModuleInst := { types := [sigB, sigA, callerAType], tables := [⟨0⟩] }
private def moduleB : Runtime.ModuleInst := { types := [sigA, sigB, callerBType], tables := [⟨1⟩] }
private def callerA : Frame := ⟨[i64 42, i32 0, i32 91], moduleA⟩
private def callerB : Frame := ⟨[i32 0, i64 17], moduleB⟩

private def read (i : LocalIdx) : Graph.Op := .numeric (.get i)
private def calleeA : Graph.Function := ⟨⟨{ types := [sigA] }, ⟨0⟩, sigA.params, [], sigA.results⟩, 0, [], [read ⟨0⟩]⟩
private def calleeB : Graph.Function := ⟨⟨{ types := [sigB] }, ⟨0⟩, [], [], sigB.results⟩, 0, [i32 29], []⟩
private def ownerA : Graph.Function :=
  ⟨⟨moduleA, ⟨2⟩, callerAType.params, [], callerAType.results⟩, 0, [i32 7], [read ⟨0⟩, read ⟨2⟩]⟩
private def ownerB : Graph.Function :=
  ⟨⟨moduleB, ⟨2⟩, callerBType.params, [], callerBType.results⟩, 0, [i64 8], [read ⟨0⟩, read ⟨1⟩]⟩
private def functions := [calleeA, calleeB, ownerA, ownerB]
private def program : Graph.Program := ⟨functions.map some⟩

private def tableA : Runtime.TableInst := ⟨[some ⟨0⟩], some 1⟩
private def tableB : Runtime.TableInst := ⟨[some ⟨1⟩, none, some ⟨0⟩], some 3⟩
private def tables : Tables := [tableA, tableB]

private def opA : Source.Op := ⟨⟨1⟩, sigA⟩
private def opB : Source.Op := ⟨⟨1⟩, sigB⟩
private def bodyA : Source.Body := .indirect [.get ⟨0⟩, .get ⟨1⟩] opA [read ⟨2⟩]
private def bodyB : Source.Body :=
  .block (some (.int .i32)) (.indirect [.get ⟨0⟩] opB []) [read ⟨1⟩]

example : program.checkDirect = true := rfl
example : bodyA.check program tables ⟨2⟩ = true := rfl
example : bodyB.check program tables ⟨3⟩ = true := rfl
example : bodyA.check program tables ⟨3⟩ = false := rfl
example : bodyB.check program [tableA] ⟨3⟩ = false := rfl
example : bodyB.core =
    [Graph.coreCodeSyntax.block (some (.int .i32)) [.localGet ⟨0⟩, .callIndirect tableIndex ⟨1⟩], .localGet ⟨1⟩] := rfl
example : bodyB.lime =
    [Graph.limeCodeSyntax.block (some (.int .i32)) [.localGet ⟨0⟩, .callIndirect ⟨1⟩], .localGet ⟨1⟩] := rfl

private def stackA : List Value := [i32 7, i64 42, i32 0]
private def activeA : Activation := ⟨callerA, ⟨⟨0⟩, ⟨tableA, ⟨1⟩, sigA⟩⟩, ⟨[i32 7], [i64 42], 0⟩⟩
private def activeB (selector : BitVec 32) : Activation :=
  ⟨callerB, ⟨⟨1⟩, ⟨tableB, ⟨1⟩, sigB⟩⟩, ⟨[], [], selector⟩⟩

private theorem preparedA : opA.Prepared program tables callerA stackA activeA := prepare_spec rfl
private theorem preparedB (selector : BitVec 32) :
    opB.Prepared program tables callerB [i32 selector] (activeB selector) := prepare_spec rfl

example : ∃ active, bodyB.operation.prepare program tables callerB [i32 0] = some active :=
  prepare_of_check (next := [.int .i32])
    (region_binding (body := bodyB) (fn := ownerB) (fallthrough := callerBType.results)
      (enclosing := []) (stack := [.int .i64]) rfl) rfl

-- Both source operators use type index one, which denotes different signatures
-- in the two modules. The table slots lead to different store addresses.
example : activeA.resolve program = some (.resolved ⟨0⟩) := rfl
example : (activeB 0).resolve program = some (.resolved ⟨1⟩) := rfl
example : opA.prepare program tables callerB stackA = none := rfl
example : opA.prepare program tables callerA [i32 7, i64 42, i64 0] = none := rfl
example : opA.prepare program tables callerA [i32 7, i32 42, i32 0] = none := rfl
example : opA.prepare program tables callerA [i32 0] = none := rfl
example : ({ opA with typeIndex := ⟨99⟩ }).prepare program tables callerA stackA = none := rfl
example : opA.prepare program [⟨[some ⟨99⟩], none⟩] callerA stackA = none := rfl
example : opA.prepare program tables { callerA with module := { moduleA with tables := [] } } stackA = none := rfl

-- These valid preparations reach native traps. A valid declaration with a
-- different signature remains distinguishable from a dangling declaration.
example : (activeB (-1)).resolve program = some .bounds := rfl
example : (activeB 1).resolve program = some .null := rfl
example : (activeB 2).resolve program = some (.mismatch ⟨0⟩) := rfl
example : (activeB 2).invocation program = none := rfl

private def coreStore : Core.Store Unit :=
  { funcs := functions.map Graph.Function.coreInstance, tables := tables.map Runtime.TableInst.toCore }
private def limeStore : Lime1.Execution.Store Unit :=
  { funcs := functions.map fun fn => .wasm fn.declaration.type fn.declaration.module fn.limeFunc
    tables := tables }

private theorem coreAllocated : program.CoreAllocated coreStore := by
  intro addr fn found
  cases slot : functions[addr.value]? <;> simp_all [Graph.Program.lookup, program, coreStore, List.getElem?_map]
private theorem limeAllocated : program.LimeAllocated limeStore := by
  intro addr fn found
  cases slot : functions[addr.value]? <;> simp_all [Graph.Program.lookup, program, limeStore, List.getElem?_map]

private theorem coreTables : Tables.CoreAllocated tables coreStore := by
  intro addr table found
  simp [coreStore, List.getElem?_map, found]
private theorem limeTables : Tables.LimeAllocated tables limeStore := fun _ _ found => found

example : ¬ Tables.CoreAllocated tables { coreStore with tables := [tableA.toCore] } := by
  intro allocated
  have impossible := allocated ⟨1⟩ tableB rfl
  cases impossible

example : ¬ program.LimeAllocated { limeStore with funcs := [.host sigA ()] } := by
  intro allocated
  have impossible := allocated ⟨0⟩ calleeA rfl
  cases impossible

private def callA : Context.Invocation := ⟨activeA.binding.site, callerA, 0, [i32 7], [i64 42], ⟨0⟩, calleeA⟩
private def callB : Context.Invocation := ⟨(activeB 0).binding.site, callerB, 0, [], [], ⟨1⟩, calleeB⟩
private theorem invokedA : activeA.invocation program = some callA := rfl
private theorem invokedB : (activeB 0).invocation program = some callB := rfl

private abbrev spec := Numerics.Profile.spec
private def scopes := bodyB.scopes [i64 8]

-- The innermost lookup and entry leave the surrounding scalar label,
-- its saved operand, and its observable local-read tail in place.
example := Source.core_resolution (P := spec) (s := coreStore)
  (preparedB 0).checked coreAllocated coreTables (out := .resolved ⟨1⟩) rfl scopes bodyB.siteTail
example := Source.core_resolution (P := spec) (s := coreStore)
  (preparedB 2).checked coreAllocated coreTables (out := .mismatch ⟨0⟩) rfl scopes bodyB.siteTail
example (dst : Lime1.Execution.Config Unit) :=
  Source.lime_resolution (s := limeStore) (preparedB 0).checked limeAllocated limeTables
    (out := .resolved ⟨1⟩) rfl scopes bodyB.siteTail dst
example (dst : Lime1.Execution.Config Unit) :=
  Source.lime_resolution (s := limeStore) (preparedB 2).checked limeAllocated limeTables
    (out := .mismatch ⟨0⟩) rfl scopes bodyB.siteTail dst

example (dst : Core.Config Unit) :
    Core.Step spec noHost ((activeB 0).coreConfig coreStore scopes [] (.call (some ⟨1⟩))) dst ↔
      dst = ⟨coreStore, callerB.toCore, coreValues [i64 8] ++
        [.label 1 [] [.frame 1 (calleeB.declaration.frame []).toCore
          [.label 1 [] [Core.constI32 29]]], .plain (.localGet ⟨1⟩)]⟩ := by
  -- The entered callee has its own module and an empty local vector.
  exact Source.core_entry (P := spec) (s := coreStore)
    (preparedB 0).checked coreAllocated invokedB scopes [] dst

example (dst : Lime1.Execution.Config Unit) :=
  Source.lime_entry (s := limeStore) (preparedB 0).checked limeAllocated invokedB scopes bodyB.siteTail dst

private def continuation : Context.Resume.Continuation := ⟨⟨2⟩, ownerA, bodyA.siteTail⟩
private theorem callChecked : callA.Checked program := invocation_checked preparedA.checked rfl invokedA
private theorem continuationChecked : continuation.Checked program callerA [i32 7] sigA.results :=
  resume_checked preparedA invokedA rfl rfl rfl rfl
private def outer : Frame := ⟨[i32 19], {}⟩

-- The same preparation discharges all site-side premises of #3060.
example (dst : Core.Config Unit) :=
  Context.Resume.core_run_iff (P := spec) (s := coreStore) (outer := outer) callChecked coreAllocated
    continuationChecked (invocation_core_table preparedA.checked coreTables invokedA) (dst := dst)
example (dst : Lime1.Execution.Config Unit) :=
  Context.Resume.lime_run_iff (s := limeStore) (outer := outer) callChecked limeAllocated
    continuationChecked (invocation_lime_table preparedA.checked limeTables invokedA) (dst := dst)

private theorem calleeReturned : program.FrameRuns ⟨0⟩ callA.entered (.done (.values [i64 42])) := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) callChecked.found).mpr
  have fetched := Relation.ReflTransGen.single (edge (.numeric (locals := [i64 42])
    (rest := []) (.get (stack := []) (i := ⟨0⟩) (v := i64 42) rfl)))
  exact (fetched.tail (edge (.leaveValues [i64 42] [i64 42]))).tail
    (edge (.leaveFrame [i64 42] (.values [i64 42]) rfl))

private def resultsA : List Value := [i32 7, i64 42, i32 91]
private theorem finished :
    Context.Resume.Runs program callA continuation (.callee callA.entered) (.caller (.done (.values resultsA))) := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) continuationChecked.found).mpr
  have returnPath := Context.Resume.of_callee_run (cont := continuation) callChecked calleeReturned
  have observed := returnPath.tail (.resume (edge (.numeric (locals := callerA.locals)
    (rest := []) (.get (stack := [i32 7, i64 42]) (i := ⟨2⟩) (v := i32 91) rfl))))
  exact (observed.tail (.caller (edge (.leaveValues callerA.locals resultsA)))).tail
    (.caller (edge (.leaveFrame callerA.locals (.values resultsA) rfl)))

example : Core.Steps spec noHost (continuation.coreWrap outer (activeA.coreConfig coreStore [] bodyA.siteTail .start))
    ⟨coreStore, outer.toCore, coreValues resultsA⟩ :=
  (Context.Resume.core_run_iff callChecked coreAllocated continuationChecked
    (invocation_core_table preparedA.checked coreTables invokedA)).mpr (.inr ⟨_, finished, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (continuation.limeWrap outer (activeA.limeSource limeStore [] bodyA.siteTail))
    ⟨limeStore, outer, Lime1.Execution.values resultsA⟩ :=
  (Context.Resume.lime_run_iff callChecked limeAllocated continuationChecked
    (invocation_lime_table preparedA.checked limeTables invokedA)).mpr (.inr ⟨_, finished, rfl⟩)
