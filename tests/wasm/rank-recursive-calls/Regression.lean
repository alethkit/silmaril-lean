module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Runtime (FuncAddr Value)

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

private abbrev i32 := Value.int .i32
private abbrev int32 := NumType.int .i32
private def input : List Value := [i32 7]
private def saved : List Value := [i32 1]
private def readArg : Op := .numeric (.get ⟨0⟩)
private def add : Op := .numeric (.bin .i32 .add)

private def declaration (targets : List FuncAddr) : Declaration :=
  ⟨{ funcs := targets }, ⟨0⟩, [int32], [], [int32]⟩

private def leaf (traps : Bool) : Function :=
  ⟨declaration [], 0, [], if traps then [.unreachable] else [readArg]⟩

private def caller (address : FuncAddr) (child : Function) : Function :=
  ⟨declaration [address], child.rank + 1, saved,
    [readArg, .call ⟨⟨0⟩, address, child.declaration⟩, add]⟩

private def middle (traps : Bool) : Function := caller ⟨0⟩ (leaf traps)
private def enclosing (traps : Bool) : Function := caller ⟨1⟩ (middle traps)
private def outer (traps : Bool) : Function := caller ⟨2⟩ (enclosing traps)

private def graph (traps : Bool) : Program :=
  ⟨[some (leaf traps), some (middle traps), some (enclosing traps), some (outer traps)]⟩

private theorem checked (traps : Bool) : (graph traps).check = true := by cases traps <;> rfl

example : (graph false).checkV1 = true := rfl

example : (Program.mk ((graph false).functions.modify 3
    (Option.map fun fn => { fn with rank := 2 }))).check = false := rfl

private def leafAt (traps : Bool) : Phase := .label input (.running [] (leaf traps).code)

private def suspended (address : FuncAddr) (child : Function) (q : Phase) : Phase :=
  .label input (.active saved ⟨⟨0⟩, address, child.declaration⟩ q [add])

private def deepest (traps : Bool) : Phase :=
  suspended ⟨2⟩ (enclosing traps) (suspended ⟨1⟩ (middle traps) (suspended ⟨0⟩ (leaf traps) (leafAt traps)))

example : (deepest false).frames ⟨3⟩ = [⟨3⟩, ⟨2⟩, ⟨1⟩, ⟨0⟩] := rfl
example : (deepest true).frames ⟨3⟩ = [⟨3⟩, ⟨2⟩, ⟨1⟩, ⟨0⟩] := rfl

private theorem enters {program : Program} (valid : program.check = true)
    {owner addr : FuncAddr} {fn : Function} (found : program.lookup owner = some (caller addr fn))
    (oneParam : fn.declaration.params = [int32]) :
    program.Runs valid owner (.invoke input) (suspended addr fn (.invoke input)) := by
  have entry := (program.edge_iff valid found).mpr (.enter input rfl)
  have get := (program.edge_iff valid found).mpr (.numeric (args := input)
    (rest := [.call ⟨⟨0⟩, addr, fn.declaration⟩, add]) (.get (stack := saved) (i := ⟨0⟩) (v := i32 7) (by rfl)))
  have dispatch := (program.edge_iff valid found).mpr
    (.dispatch input saved input ⟨⟨0⟩, addr, fn.declaration⟩ [add] (by simp [caller, Function.targets])
      (by simp [input, oneParam]))
  exact ((Relation.ReflTransGen.single entry).tail get).tail dispatch

private theorem lift {program : Program} (valid : program.check = true)
    {owner addr : FuncAddr} {fn : Function} (found : program.lookup owner = some (caller addr fn))
    {a b : Phase} (live : a.Active) (run : program.Runs valid addr a b) :
    program.Runs valid owner (suspended addr fn a)
      (.label input (Body.attach saved ⟨⟨0⟩, addr, fn.declaration⟩ [add] b)) :=
  program.lift_child valid found (by simp [caller, Function.targets]) live run

private theorem reaches (traps : Bool) :
    (graph traps).Runs (checked traps) ⟨3⟩ (.call input) (deepest traps) := by
  let p := graph traps
  have leafEntry : p.Runs (checked traps) ⟨0⟩ (.invoke input) (leafAt traps) :=
    .single ((p.edge_iff (checked traps) (fn := leaf traps) rfl).mpr (.enter input rfl))
  have middleEntry := (enters (checked traps) (owner := ⟨1⟩) (addr := ⟨0⟩) (fn := leaf traps) rfl rfl).trans
    (lift (checked traps) (addr := ⟨0⟩) (fn := leaf traps) rfl (by trivial) leafEntry)
  have parentEntry := (enters (checked traps) (owner := ⟨2⟩) (addr := ⟨1⟩) (fn := middle traps) rfl rfl).trans
    (lift (checked traps) (addr := ⟨1⟩) (fn := middle traps) rfl (by trivial) middleEntry)
  have outerEntry := (enters (checked traps) (owner := ⟨3⟩) (addr := ⟨2⟩) (fn := enclosing traps) rfl rfl).trans
    (lift (checked traps) (addr := ⟨2⟩) (fn := enclosing traps) rfl (by trivial) parentEntry)
  exact (Relation.ReflTransGen.single
    ((p.edge_iff (checked traps) (fn := outer traps) rfl).mpr (.resolve input))).trans outerEntry

example (traps : Bool) : (graph traps).table.Nesting ((deepest traps).frames ⟨3⟩) :=
  (graph traps).nesting_of_admitted (checked traps) (fn := outer traps) rfl
    ((graph traps).admitted_run (checked traps) rfl (.call rfl) (reaches traps))

private theorem leafReturns : (graph false).Runs (checked false) ⟨0⟩ (leafAt false) (.done (.values input)) := by
  have rule {a b : Phase} := (Program.edge_iff (checked false) (address := ⟨0⟩) (fn := leaf false)
    (a := a) (b := b) rfl).mpr
  have get := rule (.numeric (args := input) (rest := []) (.get (stack := []) (i := ⟨0⟩) (v := i32 7) (by rfl)))
  exact ((Relation.ReflTransGen.single get).tail (rule (.leaveValues input input))).tail
    (rule (.leaveFrame input (.values input) rfl))

example : (graph false).Runs (checked false) ⟨1⟩
    (.label input (.running (saved ++ input) [.call ⟨⟨0⟩, ⟨0⟩, (leaf false).declaration⟩, add]))
    (.label input (.running (saved ++ input) [add])) :=
  (graph false).compose_call (checked false) (fn := middle false) (target := ⟨⟨0⟩, ⟨0⟩, (leaf false).declaration⟩)
    rfl (by simp [middle, caller, Function.targets]) rfl
    ((Relation.ReflTransGen.single ((Program.edge_iff (checked false) (fn := leaf false) rfl).mpr
      (.enter input rfl))).trans leafReturns)

private theorem resumes {program : Program} (valid : program.check = true)
    {addr child : FuncAddr} {fn : Function} (found : program.lookup addr = some (caller child fn))
    {n m : BitVec 32} (sum : Numerics.intBinOp .i32 .add 1 n = .ok m)
    {q : Phase} (live : q.Active) (run : program.Runs valid child q (.done (.values [i32 n]))) :
    program.Runs valid addr (suspended child fn q) (.done (.values [i32 m])) := by
  have rule {a b : Phase} := (Program.edge_iff valid (a := a) (b := b) found).mpr
  have returns := lift valid found live run
  exact ((returns.tail (rule (.numeric (.bin (stack := []) sum)))).tail (rule (.leaveValues input [i32 m]))).tail
    (rule (.leaveFrame input (.values [i32 m]) rfl))

private theorem finishSuccess : (graph false).Runs (checked false) ⟨3⟩ (deepest false) (.done (.values [i32 10])) :=
  resumes (checked false) (fn := enclosing false) rfl rfl (by trivial)
    (resumes (checked false) (fn := middle false) rfl rfl (by trivial)
      (resumes (checked false) (fn := leaf false) rfl rfl (by trivial) leafReturns))

example : (graph false).Runs (checked false) ⟨3⟩ (.call input) (.done (.values [i32 10])) :=
  (reaches false).trans finishSuccess

private theorem leafTraps : (graph true).Runs (checked true) ⟨0⟩ (leafAt true) (.done .trap) := by
  have rule {a b : Phase} := (Program.edge_iff (checked true) (address := ⟨0⟩) (fn := leaf true)
    (a := a) (b := b) rfl).mpr
  exact ((Relation.ReflTransGen.single (rule (.unreachable input [] []))).tail
    (rule (.leaveTrap input))).tail (rule (.leaveFrame input .trap trivial))

private theorem unwinds {program : Program} (valid : program.check = true)
    {addr child : FuncAddr} {fn : Function} (found : program.lookup addr = some (caller child fn))
    {q : Phase} (live : q.Active) (run : program.Runs valid child q (.done .trap)) :
    program.Runs valid addr (suspended child fn q) (.done .trap) := by
  have rule {a b : Phase} := (Program.edge_iff valid (a := a) (b := b) found).mpr
  have trapped := lift valid found live run
  have cutCode := trapped.tail (rule (.discard (.cut saved [] [add] [] (.inr (by simp)))))
  have cutStack := cutCode.tail (rule (.discard (.cut [] saved [] [] (.inl (by simp [saved])))))
  exact (cutStack.tail (rule (.leaveTrap input))).tail (rule (.leaveFrame input .trap trivial))

private theorem finishTrap : (graph true).Runs (checked true) ⟨3⟩ (deepest true) (.done .trap) :=
  unwinds (checked true) (fn := enclosing true) rfl (by trivial)
    (unwinds (checked true) (fn := middle true) rfl (by trivial)
      (unwinds (checked true) (fn := leaf true) rfl (by trivial) leafTraps))

example : (graph true).Runs (checked true) ⟨3⟩ (.call input) (.done .trap) :=
  (reaches true).trans finishTrap

private def multiResult : Function :=
  { leaf false with
    declaration := { (leaf false).declaration with results := [.int .i64, int32] }
    initial := [Value.int .i64 11] }

private def multiGraph : Program := ⟨[some multiResult]⟩

private theorem multiChecked : multiGraph.check = true := rfl
example : multiGraph.checkV1 = false := rfl

private theorem multiRun : multiGraph.Runs multiChecked ⟨0⟩ (.invoke input) (.done (.values [Value.int .i64 11, i32 7])) := by
  have rule {a b : Phase} := (Program.edge_iff multiChecked (address := ⟨0⟩) (fn := multiResult)
    (a := a) (b := b) rfl).mpr
  have enter := rule (.enter input rfl)
  have readLocal := rule (.numeric (args := input) (rest := []) (.get (stack := [Value.int .i64 11])
    (i := ⟨0⟩) (v := i32 7) (by rfl)))
  exact (((Relation.ReflTransGen.single enter).tail readLocal).tail (rule (.leaveValues input _))).tail
    (rule (.leaveFrame input (.values [Value.int .i64 11, i32 7]) rfl))

open Silmaril.Wasm.Execution.Core in
example (s : Store Unit) (caller parent child : Frame) :
    Step Numerics.Profile.spec SingleThreaded.Det.noHost
      ⟨s, caller, [.frame 1 parent [.label 1 [] [.plain (.intConst .i32 1),
        .frame 1 child [.plain (.intConst .i32 7)], .plain (.intBinOp .i32 .add)]]]⟩
      ⟨s, caller, [.frame 1 parent [.label 1 [] [.plain (.intConst .i32 1),
        .plain (.intConst .i32 7), .plain (.intBinOp .i32 .add)]]]⟩ :=
  (core_entered_child_iff (saved := [(i32 1).toCore])).mpr
    ⟨⟨s, parent, [.plain (.intConst .i32 7)]⟩, .frameVals (vs := [(i32 7).toCore]) rfl, rfl⟩

open Silmaril.Wasm.Lime1.Execution in
example (s : Store Unit) (caller parent child : Execution.Runtime.Frame) :
    Step CallFrame.limeNoHost
      ⟨s, caller, [.frame 1 parent [.label 1 [] [.source (.intConst .i32 1),
        .frame 1 child [.trap], .source (.intBinOp .i32 .add)]]]⟩
      ⟨s, caller, [.frame 1 parent [.label 1 [] [.source (.intConst .i32 1),
        .trap, .source (.intBinOp .i32 .add)]]]⟩ :=
  (lime_entered_child_iff (saved := saved)).mpr
    ⟨⟨s, parent, [.trap]⟩, .pure s parent (.frameTrap 1 child), rfl⟩

private def callerFrame (address : FuncAddr) : Execution.Runtime.Frame :=
  ⟨[i32 41], { funcs := [address] }⟩

private def rootTarget (traps : Bool) : CallTarget := ⟨⟨0⟩, ⟨3⟩, (outer traps).declaration⟩

private theorem root (traps : Bool) :
    Root (graph traps) (callerFrame ⟨3⟩) (rootTarget traps) (outer traps) :=
  ⟨rfl, rfl, rfl⟩

private def allocate {A : Type} (program : Program) (instantiate : Function → A) : List A :=
  program.functions.map fun slot => instantiate (slot.getD (leaf false))

private theorem allocated_at {A : Type} (program : Program) (instantiate : Function → A)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    (allocate program instantiate)[address.value]? = some (instantiate fn) := by
  unfold allocate
  rw [List.getElem?_map]
  unfold Program.lookup at found
  cases h : program.functions[address.value]? with
  | none => simp [h] at found
  | some slot =>
    cases slot with
    | none => simp [h] at found
    | some stored => simpa [h] using congrArg (Option.map instantiate) found

private def coreStore (program : Program) : Execution.Core.Store Unit :=
  { funcs := allocate program Function.coreInstance }

private def limeStore (program : Program) : Lime1.Execution.Store Unit :=
  { funcs := allocate program fun fn => .wasm fn.declaration.type fn.declaration.module fn.limeFunc }

private def v1Store (program : Program) : V1.Execution.Store Unit :=
  { funcs := allocate program fun fn => .wasm fn.declaration.type fn.declaration.module fn.v1Func }

private theorem coreAllocated (program : Program) : program.CoreAllocated (coreStore program) :=
  fun _ _ found => allocated_at program Function.coreInstance found

private theorem limeAllocated (program : Program) : program.LimeAllocated (limeStore program) :=
  fun _ _ found => allocated_at program
    (fun fn => (Execution.Runtime.FuncInst.wasm fn.declaration.type fn.declaration.module fn.limeFunc :
      Execution.Runtime.FuncInst Lime1.Func Unit)) found

private theorem v1Allocated (program : Program) : program.V1Allocated (v1Store program) :=
  fun _ _ found => allocated_at program
    (fun fn => (Execution.Runtime.FuncInst.wasm fn.declaration.type fn.declaration.module fn.v1Func :
      Execution.Runtime.FuncInst V1.Func Unit)) found

private theorem v1Checked (traps : Bool) : (graph traps).checkV1 = true := by cases traps <;> rfl

private theorem deepestReady (traps : Bool) : Admitted (graph traps) (outer traps) (deepest traps) :=
  (graph traps).admitted_run (checked traps) rfl (.call rfl) (reaches traps)

private def outcome (traps : Bool) : Nested.Result := if traps then .trap else .values [i32 10]

private theorem finishes (traps : Bool) :
    (graph traps).Runs (checked traps) ⟨3⟩ (deepest traps) (.done (outcome traps)) := by
  cases traps
  · exact finishSuccess
  · exact finishTrap

private theorem outcomeReady (traps : Bool) : Admitted (graph traps) (outer traps) (.done (outcome traps)) :=
  (graph traps).admitted_run (checked traps) rfl (deepestReady traps) (finishes traps)

private theorem coreTrace (traps : Bool) :
    Execution.Core.Steps Numerics.Profile.spec SingleThreaded.Det.noHost
      (coreConfig (coreStore (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) (.call input))
      (coreConfig (coreStore (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) (.done (outcome traps))) := by
  have nested := (core_run_iff (P := Numerics.Profile.spec) (checked traps) (coreAllocated _) (root traps)
    (.call rfl)).mpr ⟨_, reaches traps, deepestReady traps, rfl⟩
  have exit := (core_run_iff (P := Numerics.Profile.spec) (checked traps) (coreAllocated _) (root traps)
    (deepestReady traps)).mpr ⟨_, finishes traps, outcomeReady traps, rfl⟩
  exact nested.trans exit

private theorem limeTrace (traps : Bool) :
    Lime1.Execution.Steps CallFrame.limeNoHost
      (limeConfig (limeStore (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) (.call input))
      (limeConfig (limeStore (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) (.done (outcome traps))) := by
  have nested := (lime_run_iff (checked traps) (limeAllocated _) (root traps) (.call rfl)).mpr
    ⟨_, reaches traps, deepestReady traps, rfl⟩
  have exit := (lime_run_iff (checked traps) (limeAllocated _) (root traps) (deepestReady traps)).mpr
    ⟨_, finishes traps, outcomeReady traps, rfl⟩
  exact nested.trans exit

private theorem v1Trace (traps : Bool) :
    V1.Execution.Steps CallFrame.v1NoHost
      (v1Config (v1Store (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) (.call input))
      (v1Config (v1Store (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) (.done (outcome traps))) := by
  have nested := (v1_run_iff (v1Checked traps) (v1Allocated _) (root traps) (.call rfl)).mpr
    ⟨_, reaches traps, deepestReady traps, rfl⟩
  have exit := (v1_run_iff (v1Checked traps) (v1Allocated _) (root traps) (deepestReady traps)).mpr
    ⟨_, finishes traps, outcomeReady traps, rfl⟩
  exact nested.trans exit

example : Execution.Core.Steps Numerics.Profile.spec SingleThreaded.Det.noHost
    ⟨coreStore (graph false), (callerFrame ⟨3⟩).toCore, [.plain (.intConst .i32 7), .plain (.call ⟨0⟩)]⟩
    ⟨coreStore (graph false), (callerFrame ⟨3⟩).toCore, [.plain (.intConst .i32 10)]⟩ :=
  coreTrace false

example : Lime1.Execution.Steps CallFrame.limeNoHost
    ⟨limeStore (graph true), callerFrame ⟨3⟩, [.source (.intConst .i32 7), .source (.call ⟨0⟩)]⟩
    ⟨limeStore (graph true), callerFrame ⟨3⟩, [.trap]⟩ :=
  limeTrace true

example : V1.Execution.Steps CallFrame.v1NoHost
    ⟨v1Store (graph true), callerFrame ⟨3⟩, [.source (.intConst .i32 7), .source (.call ⟨0⟩)]⟩
    ⟨v1Store (graph true), callerFrame ⟨3⟩, [.trap]⟩ :=
  v1Trace true

example (traps : Bool) {dst : Execution.Core.Config Unit}
    (step : Execution.Core.Step Numerics.Profile.spec SingleThreaded.Det.noHost
      (coreConfig (coreStore (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) (deepest traps)) dst) :
    ∃ out, (graph traps).Edge (checked traps) ⟨3⟩ (deepest traps) out ∧
      dst = coreConfig (coreStore (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) out :=
  (core_step_iff (checked traps) (coreAllocated _) (root traps) (deepestReady traps)).mp step

example (traps : Bool) {dst : Lime1.Execution.Config Unit}
    (trace : Lime1.Execution.Steps CallFrame.limeNoHost
      (limeConfig (limeStore (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) (deepest traps)) dst) :
    ∃ out, (graph traps).Runs (checked traps) ⟨3⟩ (deepest traps) out ∧ Admitted (graph traps) (outer traps) out ∧
      dst = limeConfig (limeStore (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) out :=
  (lime_run_iff (checked traps) (limeAllocated _) (root traps) (deepestReady traps)).mp trace

example (traps : Bool) {dst : Lime1.Execution.Config Unit}
    (step : Lime1.Execution.Step CallFrame.limeNoHost
      (v1Config (v1Store (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) (deepest traps)).toLime dst) :
    ∃ mid, V1.Execution.Step CallFrame.v1NoHost
      (v1Config (v1Store (graph traps)) (callerFrame ⟨3⟩) (rootTarget traps) (deepest traps)) mid ∧ mid.toLime = dst :=
  v1_reflect_lime_step (v1Checked traps) (v1Allocated _) (root traps) (deepestReady traps) step

private def multiTarget : CallTarget := ⟨⟨0⟩, ⟨0⟩, multiResult.declaration⟩

private theorem multiRoot : Root multiGraph (callerFrame ⟨0⟩) multiTarget multiResult :=
  ⟨rfl, rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeConfig (limeStore multiGraph) (callerFrame ⟨0⟩) multiTarget (.invoke input))
    ⟨limeStore multiGraph, callerFrame ⟨0⟩, [.source (.intConst .i64 11), .source (.intConst .i32 7)]⟩ :=
  (lime_run_iff multiChecked (limeAllocated _) multiRoot (.invoke rfl)).mpr ⟨_, multiRun, .done rfl, rfl⟩

example : Execution.Core.Steps Numerics.Profile.spec SingleThreaded.Det.noHost
    (coreConfig (coreStore multiGraph) (callerFrame ⟨0⟩) multiTarget (.invoke input))
    ⟨coreStore multiGraph, (callerFrame ⟨0⟩).toCore, [.plain (.intConst .i64 11), .plain (.intConst .i32 7)]⟩ :=
  (core_run_iff (P := Numerics.Profile.spec) multiChecked (coreAllocated _) multiRoot (.invoke rfl)).mpr
    ⟨_, multiRun, .done rfl, rfl⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
