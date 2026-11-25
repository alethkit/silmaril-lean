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
  have get := (program.edge_iff valid found).mpr (.numeric (locals := input)
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
  have get := rule (.numeric (locals := input) (rest := []) (.get (stack := []) (i := ⟨0⟩) (v := i32 7) (by rfl)))
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
  have readLocal := rule (.numeric (locals := input) (rest := []) (.get (stack := [Value.int .i64 11])
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

private def readSecond : Op := .numeric (.get ⟨1⟩)
private def leafRest (traps : Bool) : List Op := if traps then [.unreachable] else [readArg, add]

private def writingLeaf (traps : Bool) : Function :=
  ⟨{ declaration [] with locals := [int32] }, 0, [i32 2],
    [.set ⟨1⟩, readArg, readSecond, add, .tee ⟨0⟩] ++ leafRest traps⟩

private def writingTarget (traps : Bool) : CallTarget := ⟨⟨0⟩, ⟨0⟩, (writingLeaf traps).declaration⟩

private def parentRest : List Op := [readArg, add, .set ⟨1⟩, readSecond, add]

private def writingParent (traps : Bool) : Function :=
  ⟨{ declaration [⟨0⟩] with locals := [int32] }, 1, [i32 4],
    [.set ⟨0⟩, readArg, readArg, .call (writingTarget traps)] ++ parentRest⟩

private def writingGraph (traps : Bool) : Program := ⟨[some (writingLeaf traps), some (writingParent traps)]⟩

private theorem writingChecked (traps : Bool) : (writingGraph traps).check = true := by cases traps <;> rfl
private theorem writingV1Checked (traps : Bool) : (writingGraph traps).checkV1 = true := by cases traps <;> rfl

private def invalidWrite (op : Op) (v : Value) : Program :=
  ⟨[some { writingLeaf false with initial := [v], code := [op, .unreachable] }]⟩

example : (invalidWrite (.set ⟨2⟩) (i32 1)).check = false := rfl
example : (invalidWrite (.tee ⟨0⟩) (Value.int .i64 1)).check = false := rfl

private def beforeTee (traps : Bool) : Phase :=
  .label [i32 4, i32 2] (.running [i32 6] (.tee ⟨0⟩ :: leafRest traps))

private def afterTee (traps : Bool) : Phase :=
  .label [i32 4, i32 2] (.running [i32 6, i32 6] (.set ⟨0⟩ :: leafRest traps))

private def afterWrite (traps : Bool) : Phase :=
  .label [i32 6, i32 2] (.running [i32 6] (leafRest traps))

private theorem leafRule (traps : Bool) {a b : Phase} :
    Layer (writingLeaf traps) (fun target => (writingGraph traps).Edge (writingChecked traps) target.address) a b →
      (writingGraph traps).Edge (writingChecked traps) ⟨0⟩ a b :=
  ((writingGraph traps).edge_iff (writingChecked traps) (fn := writingLeaf traps) rfl).mpr

private theorem leafGetsToTee (traps : Bool) :
    (writingGraph traps).Runs (writingChecked traps) ⟨0⟩ (.invoke [i32 4]) (beforeTee traps) := by
  have entry := Relation.ReflTransGen.single (leafRule traps (.enter [i32 4] rfl))
  have setSecond := entry.tail (leafRule traps (.localSet (saved := []) (Locals.fact (.set [i32 4, i32 0] ⟨1⟩ (i32 2) (by decide)))))
  have getFirst := setSecond.tail (leafRule traps (.numeric (.get (stack := []) (i := ⟨0⟩) (v := i32 4) rfl)))
  have getSecond := getFirst.tail (leafRule traps (.numeric (.get (stack := [i32 4]) (i := ⟨1⟩) (v := i32 2) rfl)))
  have sum : Numerics.intBinOp .i32 .add 4 2 = .ok 6 := rfl
  exact getSecond.tail (leafRule traps (.numeric (.bin (stack := []) sum)))

private theorem leafTee (traps : Bool) :
    (writingGraph traps).Edge (writingChecked traps) ⟨0⟩ (beforeTee traps) (afterTee traps) :=
  leafRule traps (.localTee (saved := []) (Locals.fact (.tee [i32 4, i32 2] ⟨0⟩ (i32 6))))

private theorem leafWrite (traps : Bool) :
    (writingGraph traps).Edge (writingChecked traps) ⟨0⟩ (afterTee traps) (afterWrite traps) :=
  leafRule traps (.localSet (saved := [i32 6]) (Locals.fact (.set [i32 4, i32 2] ⟨0⟩ (i32 6) (by decide))))

private def suspendedWrite (traps : Bool) (q : Phase) : Phase :=
  .label [i32 4, i32 0] (.active [i32 4] (writingTarget traps) q parentRest)

private theorem parentRule (traps : Bool) {a b : Phase} :
    Layer (writingParent traps) (fun target => (writingGraph traps).Edge (writingChecked traps) target.address) a b →
      (writingGraph traps).Edge (writingChecked traps) ⟨1⟩ a b :=
  ((writingGraph traps).edge_iff (writingChecked traps) (fn := writingParent traps) rfl).mpr

private theorem usesWritingTarget (traps : Bool) : writingTarget traps ∈ (writingParent traps).targets := by
  simp [writingParent, Function.targets, parentRest, readArg, add, readSecond]

private theorem parentInvokes (traps : Bool) :
    (writingGraph traps).Runs (writingChecked traps) ⟨1⟩ (.call input) (suspendedWrite traps (.invoke [i32 4])) := by
  have resolved := Relation.ReflTransGen.single (parentRule traps (.resolve input))
  have entry := resolved.tail (parentRule traps (.enter input rfl))
  have setFirst := entry.tail (parentRule traps (.localSet (saved := []) (Locals.fact (.set [i32 7, i32 0] ⟨0⟩ (i32 4) (by decide)))))
  have savedRead := setFirst.tail (parentRule traps (.numeric (.get (stack := []) (i := ⟨0⟩) (v := i32 4) rfl)))
  have argRead := savedRead.tail (parentRule traps (.numeric (.get (stack := [i32 4]) (i := ⟨0⟩) (v := i32 4) rfl)))
  exact argRead.tail (parentRule traps (.dispatch [i32 4, i32 0] [i32 4] [i32 4] _ parentRest (usesWritingTarget traps) rfl))

private theorem liftWriteRun (traps : Bool) {a b : Phase} (live : a.Active)
    (run : (writingGraph traps).Runs (writingChecked traps) ⟨0⟩ a b) :
    (writingGraph traps).Runs (writingChecked traps) ⟨1⟩ (suspendedWrite traps a)
      (.label [i32 4, i32 0] (Body.attach [i32 4] (writingTarget traps) parentRest b)) :=
  (writingGraph traps).lift_child (writingChecked traps) (fn := writingParent traps) rfl (usesWritingTarget traps) live run

private theorem writingReached (traps : Bool) :
    (writingGraph traps).Runs (writingChecked traps) ⟨1⟩ (.call input) (suspendedWrite traps (afterWrite traps)) :=
  (parentInvokes traps).trans (liftWriteRun traps (by trivial) (((leafGetsToTee traps).tail (leafTee traps)).tail (leafWrite traps)))

private theorem leafReturnsWritten :
    (writingGraph false).Runs (writingChecked false) ⟨0⟩ (afterWrite false) (.done (.values [i32 12])) := by
  have get := leafRule false (.numeric (locals := [i32 6, i32 2]) (rest := [add])
    (.get (stack := [i32 6]) (i := ⟨0⟩) (v := i32 6) rfl))
  have sum : Numerics.intBinOp .i32 .add 6 6 = .ok 12 := rfl
  have added := (Relation.ReflTransGen.single get).tail (leafRule false (.numeric (.bin (stack := []) sum)))
  exact (added.tail (leafRule false (.leaveValues [i32 6, i32 2] [i32 12]))).tail
    (leafRule false (.leaveFrame [i32 6, i32 2] (.values [i32 12]) rfl))

private theorem writingReturns :
    (writingGraph false).Runs (writingChecked false) ⟨1⟩
      (suspendedWrite false (afterWrite false)) (.done (.values [i32 20])) := by
  have resumed := liftWriteRun false (by trivial) leafReturnsWritten
  have read := resumed.tail (parentRule false (.numeric (.get (stack := [i32 4, i32 12]) (i := ⟨0⟩) (v := i32 4) rfl)))
  have sum : Numerics.intBinOp .i32 .add 12 4 = .ok 16 := rfl
  have added := read.tail (parentRule false (.numeric (.bin (stack := [i32 4]) sum)))
  have updated := added.tail (parentRule false (.localSet (saved := [i32 4]) (Locals.fact (.set [i32 4, i32 0] ⟨1⟩ (i32 16) (by decide)))))
  have load := updated.tail (parentRule false (.numeric (.get (stack := [i32 4]) (i := ⟨1⟩) (v := i32 16) rfl)))
  have last : Numerics.intBinOp .i32 .add 4 16 = .ok 20 := rfl
  have result := load.tail (parentRule false (.numeric (.bin (stack := []) last)))
  exact (result.tail (parentRule false (.leaveValues [i32 4, i32 16] [i32 20]))).tail
    (parentRule false (.leaveFrame [i32 4, i32 16] (.values [i32 20]) rfl))

private theorem childTrapsAfterWriting :
    (writingGraph true).Runs (writingChecked true) ⟨0⟩ (afterWrite true) (.done .trap) := by
  have raised := Relation.ReflTransGen.single (leafRule true (.unreachable [i32 6, i32 2] [i32 6] []))
  have dropped := raised.tail (leafRule true (.discard (.cut [] [i32 6] [] [] (.inl (by simp)))))
  exact (dropped.tail (leafRule true (.leaveTrap [i32 6, i32 2]))).tail
    (leafRule true (.leaveFrame [i32 6, i32 2] .trap trivial))

private theorem trapReachesParent :
    (writingGraph true).Runs (writingChecked true) ⟨1⟩ (suspendedWrite true (afterWrite true))
      (.label [i32 4, i32 0] (.trapped [i32 4] parentRest)) :=
  liftWriteRun true (by trivial) childTrapsAfterWriting

private theorem writingTraps :
    (writingGraph true).Runs (writingChecked true) ⟨1⟩
      (suspendedWrite true (afterWrite true)) (.done .trap) := by
  have dropped := trapReachesParent.tail (parentRule true (.discard (.cut [] [i32 4] parentRest [] (.inl (by simp)))))
  exact (dropped.tail (parentRule true (.leaveTrap [i32 4, i32 0]))).tail
    (parentRule true (.leaveFrame [i32 4, i32 0] .trap trivial))

private def writingRootTarget (traps : Bool) : CallTarget := ⟨⟨0⟩, ⟨1⟩, (writingParent traps).declaration⟩

private theorem writingRoot (traps : Bool) :
    Root (writingGraph traps) (callerFrame ⟨1⟩) (writingRootTarget traps) (writingParent traps) := ⟨rfl, rfl, rfl⟩

example : V1.Execution.Step CallFrame.v1NoHost
    (v1Config (v1Store (writingGraph false)) (callerFrame ⟨1⟩) (writingRootTarget false)
      (suspendedWrite false (afterTee false)))
    ⟨v1Store (writingGraph false), callerFrame ⟨1⟩,
      [.frame 1 ⟨[i32 4, i32 0], (writingParent false).declaration.module⟩
        [.label 1 [] ([.source (.intConst .i32 4)] ++
          [.frame 1 ⟨[i32 6, i32 2], (writingLeaf false).declaration.module⟩
            [.label 1 [] [.source (.intConst .i32 6), .source (.localGet ⟨0⟩), .source (.intBinOp .i32 .add)]]] ++
          parentRest.map v1Admin.emit)]]⟩ := by
  have nested := liftWriteRun false (by trivial) ((leafGetsToTee false).tail (leafTee false))
  have ready := (writingGraph false).admitted_run (writingChecked false) rfl (.call rfl)
    ((parentInvokes false).trans nested)
  have write : (writingGraph false).Edge (writingChecked false) ⟨1⟩
      (suspendedWrite false (afterTee false)) (suspendedWrite false (afterWrite false)) :=
    parentRule false (.child (a := afterTee false) (b := afterWrite false) [i32 4, i32 0] [i32 4] (writingTarget false) parentRest
      (usesWritingTarget false) (by trivial) (leafWrite false))
  exact (v1_step_iff (writingV1Checked false) (v1Allocated _) (writingRoot false) ready).mpr ⟨_, write, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeConfig (limeStore (writingGraph true)) (callerFrame ⟨1⟩) (writingRootTarget true)
      (suspendedWrite true (afterWrite true)))
    ⟨limeStore (writingGraph true), callerFrame ⟨1⟩,
      [.frame 1 ⟨[i32 4, i32 0], (writingParent true).declaration.module⟩
        [.label 1 [] (.source (.intConst .i32 4) :: .trap :: parentRest.map limeAdmin.emit)]]⟩ := by
  have ready := (writingGraph true).admitted_run (writingChecked true) rfl (.call rfl) (writingReached true)
  exact (lime_run_iff (writingChecked true) (limeAllocated _) (writingRoot true) ready).mpr
    ⟨_, trapReachesParent, .trapped rfl, rfl⟩

private def writingResult (traps : Bool) : Nested.Result := if traps then .trap else .values [i32 20]

private theorem writingRun (traps : Bool) :
    (writingGraph traps).Runs (writingChecked traps) ⟨1⟩ (.call input) (.done (writingResult traps)) := by
  apply (writingReached traps).trans
  cases traps
  · exact writingReturns
  · exact writingTraps

private theorem writingResultTyped (traps : Bool) :
    Admitted (writingGraph traps) (writingParent traps) (.done (writingResult traps)) :=
  (writingGraph traps).admitted_run (writingChecked traps) rfl (.call rfl) (writingRun traps)

example (traps : Bool) : Execution.Core.Steps Numerics.Profile.spec SingleThreaded.Det.noHost
    (coreConfig (coreStore (writingGraph traps)) (callerFrame ⟨1⟩) (writingRootTarget traps) (.call input))
    (coreConfig (coreStore (writingGraph traps)) (callerFrame ⟨1⟩) (writingRootTarget traps) (.done (writingResult traps))) :=
  (core_run_iff (writingChecked traps) (coreAllocated _) (writingRoot traps) (.call rfl)).mpr
    ⟨_, writingRun traps, writingResultTyped traps, rfl⟩

example (traps : Bool) : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeConfig (limeStore (writingGraph traps)) (callerFrame ⟨1⟩) (writingRootTarget traps) (.call input))
    (limeConfig (limeStore (writingGraph traps)) (callerFrame ⟨1⟩) (writingRootTarget traps) (.done (writingResult traps))) :=
  (lime_run_iff (writingChecked traps) (limeAllocated _) (writingRoot traps) (.call rfl)).mpr
    ⟨_, writingRun traps, writingResultTyped traps, rfl⟩

example (traps : Bool) : V1.Execution.Steps CallFrame.v1NoHost
    (v1Config (v1Store (writingGraph traps)) (callerFrame ⟨1⟩) (writingRootTarget traps) (.call input))
    (v1Config (v1Store (writingGraph traps)) (callerFrame ⟨1⟩) (writingRootTarget traps) (.done (writingResult traps))) :=
  (v1_run_iff (writingV1Checked traps) (v1Allocated _) (writingRoot traps) (.call rfl)).mpr
    ⟨_, writingRun traps, writingResultTyped traps, rfl⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
