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
    (.dispatch input saved input ⟨⟨0⟩, addr, fn.declaration⟩ [add] (by simp [caller, Function.targets, codeTargets, Op.targets, readArg, add])
      (by simp [input, oneParam]))
  exact ((Relation.ReflTransGen.single entry).tail get).tail dispatch

private theorem lift {program : Program} (valid : program.check = true)
    {owner addr : FuncAddr} {fn : Function} (found : program.lookup owner = some (caller addr fn))
    {a b : Phase} (live : a.Active) (run : program.Runs valid addr a b) :
    program.Runs valid owner (suspended addr fn a)
      (.label input (Body.attach saved ⟨⟨0⟩, addr, fn.declaration⟩ [add] b)) :=
  program.lift_child valid found (by simp [caller, Function.targets, codeTargets, Op.targets, readArg, add]) live run

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
    rfl (by simp [middle, caller, Function.targets, codeTargets, Op.targets, readArg, add]) rfl
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
    initial := [i32 99, Value.int .i64 11]
    code := [readArg, .return_, .unreachable] }

private def multiGraph : Program := ⟨[some multiResult]⟩

private theorem multiChecked : multiGraph.check = true := rfl
example : multiGraph.checkV1 = false := rfl

example : ({ multiResult with initial := [], code := [.return_] }).check = false := rfl
example : ({ multiResult with initial := [i32 7, Value.int .i64 11], code := [.return_] }).check = false := rfl
example : ({ multiResult with initial := [i32 11, i32 7], code := [.return_] }).check = false := rfl

private theorem multiRun : multiGraph.Runs multiChecked ⟨0⟩ (.invoke input) (.done (.values [Value.int .i64 11, i32 7])) := by
  have rule {a b : Phase} := (Program.edge_iff multiChecked (address := ⟨0⟩) (fn := multiResult)
    (a := a) (b := b) rfl).mpr
  have enter := rule (.enter input rfl)
  have readLocal := rule (.numeric (locals := input) (rest := [.return_, .unreachable])
    (.get (stack := [i32 99, Value.int .i64 11]) (i := ⟨0⟩) (v := i32 7) rfl))
  exact (((Relation.ReflTransGen.single enter).tail readLocal).tail
    (rule (.returnLabel input [i32 99, Value.int .i64 11, i32 7] [.unreachable]))).tail
    (rule (.returnFrame input [i32 99] [Value.int .i64 11, i32 7] rfl))

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
  have nested := (v1_run_iff (v1Checked traps) (v1Allocated _) (root traps) (.call rfl) rfl).mpr
    ⟨_, reaches traps, deepestReady traps, rfl⟩
  have exit := (v1_run_iff (v1Checked traps) (v1Allocated _) (root traps) (deepestReady traps) (by cases traps <;> rfl)).mpr
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
  v1_reflect_lime_step (v1Checked traps) (v1Allocated _) (root traps) (deepestReady traps) (by cases traps <;> rfl) step

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
private def leafRest (traps : Bool) : List Op := if traps then [.unreachable] else [readArg, readArg, add, .return_, .unreachable]

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
  simp [writingParent, Function.targets, codeTargets, Op.targets, parentRest, readArg, add, readSecond]

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

private def beforeReturn : Phase :=
  .label [i32 6, i32 2] (.running [i32 6, i32 12] [.return_, .unreachable])

private def betweenReturnExits : Phase := .returning [i32 6, i32 2] [i32 6, i32 12]

private theorem leafPreparesReturn :
    (writingGraph false).Runs (writingChecked false) ⟨0⟩ (afterWrite false) beforeReturn := by
  have get := leafRule false (.numeric (locals := [i32 6, i32 2]) (rest := [readArg, add, .return_, .unreachable])
    (.get (stack := [i32 6]) (i := ⟨0⟩) (v := i32 6) rfl))
  have getAgain := leafRule false (.numeric (locals := [i32 6, i32 2]) (rest := [add, .return_, .unreachable])
    (.get (stack := [i32 6, i32 6]) (i := ⟨0⟩) (v := i32 6) rfl))
  have sum : Numerics.intBinOp .i32 .add 6 6 = .ok 12 := rfl
  exact ((Relation.ReflTransGen.single get).tail getAgain).tail (leafRule false (.numeric (.bin (stack := [i32 6]) sum)))

private theorem leafReturnLabel :
    (writingGraph false).Edge (writingChecked false) ⟨0⟩ beforeReturn betweenReturnExits :=
  leafRule false (.returnLabel [i32 6, i32 2] [i32 6, i32 12] [.unreachable])

private theorem leafReturnFrame :
    (writingGraph false).Edge (writingChecked false) ⟨0⟩ betweenReturnExits (.done (.values [i32 12])) :=
  leafRule false (.returnFrame [i32 6, i32 2] [i32 6] [i32 12] rfl)

private theorem leafReturnsWritten :
    (writingGraph false).Runs (writingChecked false) ⟨0⟩ (afterWrite false) (.done (.values [i32 12])) :=
  (leafPreparesReturn.tail leafReturnLabel).tail leafReturnFrame

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
            [.label 1 [] [.source (.intConst .i32 6), .source (.localGet ⟨0⟩), .source (.localGet ⟨0⟩),
              .source (.intBinOp .i32 .add), .source .return_, .source .unreachable]]] ++
          parentRest.map v1Admin.emit)]]⟩ := by
  have nested := liftWriteRun false (by trivial) ((leafGetsToTee false).tail (leafTee false))
  have ready := (writingGraph false).admitted_run (writingChecked false) rfl (.call rfl)
    ((parentInvokes false).trans nested)
  have write : (writingGraph false).Edge (writingChecked false) ⟨1⟩
      (suspendedWrite false (afterTee false)) (suspendedWrite false (afterWrite false)) :=
    parentRule false (.child (a := afterTee false) (b := afterWrite false) [i32 4, i32 0] [i32 4] (writingTarget false) parentRest
      (usesWritingTarget false) (by trivial) (leafWrite false))
  exact (v1_step_iff (writingV1Checked false) (v1Allocated _) (writingRoot false) ready rfl).mpr ⟨_, write, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeConfig (limeStore (writingGraph true)) (callerFrame ⟨1⟩) (writingRootTarget true)
      (suspendedWrite true (afterWrite true)))
    ⟨limeStore (writingGraph true), callerFrame ⟨1⟩,
      [.frame 1 ⟨[i32 4, i32 0], (writingParent true).declaration.module⟩
        [.label 1 [] (.source (.intConst .i32 4) :: .trap :: parentRest.map limeAdmin.emit)]]⟩ := by
  have ready := (writingGraph true).admitted_run (writingChecked true) rfl (.call rfl) (writingReached true)
  exact (lime_run_iff (writingChecked true) (limeAllocated _) (writingRoot true) ready).mpr
    ⟨_, trapReachesParent, .trapped rfl, rfl⟩

private theorem nestedReturnLabel :
    (writingGraph false).Edge (writingChecked false) ⟨1⟩
      (suspendedWrite false beforeReturn) (suspendedWrite false betweenReturnExits) :=
  parentRule false (.child (a := beforeReturn) (b := betweenReturnExits) [i32 4, i32 0] [i32 4]
    (writingTarget false) parentRest (usesWritingTarget false) trivial leafReturnLabel)

private theorem nestedReturnFrame :
    (writingGraph false).Edge (writingChecked false) ⟨1⟩
      (suspendedWrite false betweenReturnExits) (.label [i32 4, i32 0] (.running [i32 4, i32 12] parentRest)) :=
  parentRule false (.child (a := betweenReturnExits) (b := .done (.values [i32 12])) [i32 4, i32 0] [i32 4]
    (writingTarget false) parentRest (usesWritingTarget false) trivial leafReturnFrame)

private theorem beforeReturnReady : Admitted (writingGraph false) (writingParent false)
    (suspendedWrite false beforeReturn) :=
  (writingGraph false).admitted_run (writingChecked false) rfl (.call rfl)
    ((writingReached false).trans (liftWriteRun false (by trivial) leafPreparesReturn))

example : Execution.Core.Step Numerics.Profile.spec SingleThreaded.Det.noHost
    (coreConfig (coreStore (writingGraph false)) (callerFrame ⟨1⟩) (writingRootTarget false)
      (suspendedWrite false beforeReturn))
    ⟨coreStore (writingGraph false), (callerFrame ⟨1⟩).toCore,
      [.frame 1 (currentFrame (writingParent false).declaration [i32 4, i32 0]).toCore
        [.label 1 [] (.plain (.intConst .i32 4) ::
          .frame 1 (currentFrame (writingLeaf false).declaration [i32 6, i32 2]).toCore
            [.plain (.intConst .i32 6), .plain (.intConst .i32 12), .plain .return_] ::
          parentRest.map coreAdmin.emit)]]⟩ :=
  (core_step_iff (writingChecked false) (coreAllocated _) (writingRoot false) beforeReturnReady).mpr
    ⟨_, nestedReturnLabel, rfl⟩

example : V1.Execution.Step CallFrame.v1NoHost
    (v1Config (v1Store (writingGraph false)) (callerFrame ⟨1⟩) (writingRootTarget false)
      (suspendedWrite false betweenReturnExits))
    ⟨v1Store (writingGraph false), callerFrame ⟨1⟩,
      [.frame 1 (currentFrame (writingParent false).declaration [i32 4, i32 0])
        [.label 1 [] (.source (.intConst .i32 4) :: .source (.intConst .i32 12) :: parentRest.map v1Admin.emit)]]⟩ := by
  have ready := (writingGraph false).admitted_step (writingChecked false) rfl beforeReturnReady nestedReturnLabel
  exact (v1_step_iff (writingV1Checked false) (v1Allocated _) (writingRoot false) ready rfl).mpr
    ⟨_, nestedReturnFrame, rfl⟩

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
  (v1_run_iff (writingV1Checked traps) (v1Allocated _) (writingRoot traps) (.call rfl) rfl).mpr
    ⟨_, writingRun traps, writingResultTyped traps, rfl⟩


private def blockTarget (traps : Bool) : CallTarget := ⟨⟨0⟩, ⟨0⟩, (leaf traps).declaration⟩
private def blockHead (traps : Bool) : List Op := [readArg, .call (blockTarget traps)]
private def blockTail : List Op := [readArg, add]
private def blockSaved : List Value := [i32 3]
private def scalarBlock : Option NumType := some int32
private def wideBlock : Option NumType := some (.int .i64)
private def skipped : List Op := [.unreachable]
private def returningBlock (traps : Bool) : List Op :=
  [.block wideBlock (blockHead traps ++ .return_ :: skipped)] ++ skipped

private def blockCaller (early traps : Bool) : Function :=
  ⟨declaration [⟨0⟩], 1, blockSaved,
    if early then [.block none (returningBlock traps)] ++ skipped
    else [.block scalarBlock (blockHead traps ++ blockTail), add]⟩

private def blockGraph (early traps : Bool) : Program :=
  ⟨[some (leaf traps), some (blockCaller early traps)]⟩

private theorem blockChecked (early traps : Bool) : (blockGraph early traps).check = true := by
  cases early <;> cases traps <;> rfl

private theorem blockV1Checked (early traps : Bool) : (blockGraph early traps).checkV1 = true := by
  cases early <;> cases traps <;> rfl

-- The outer saved operand is inaccessible to the block. Its fallthrough needs i64.
example : ({ blockCaller false false with code := [.block wideBlock [], .unreachable] }).check = false := rfl
example : ({ blockCaller false false with code := [.block none [.return_], .unreachable] }).check = false := rfl

-- A call hidden inside a block still has to decrease rank.
example : (Program.mk [some (leaf false), some { blockCaller false false with rank := 0 }]).check =
    false := rfl

private abbrev BlockLayer (early traps : Bool) :=
  Layer (blockCaller early traps) (fun target => (blockGraph early traps).Edge (blockChecked early traps) target.address)

private theorem blockEdge (early traps : Bool) {a b : Phase} (h : BlockLayer early traps a b) :
    (blockGraph early traps).Edge (blockChecked early traps) ⟨1⟩ a b :=
  ((blockGraph early traps).edge_iff (blockChecked early traps) (fn := blockCaller early traps) rfl).mpr h

private theorem childEdge (early traps : Bool) {a b : Phase}
    (h : Layer (leaf traps) (fun target => (blockGraph early traps).Edge (blockChecked early traps) target.address) a b) :
    (blockGraph early traps).Edge (blockChecked early traps) ⟨0⟩ a b :=
  ((blockGraph early traps).edge_iff (blockChecked early traps) (fn := leaf traps) rfl).mpr h

private theorem blockUsed (early traps : Bool) : blockTarget traps ∈ (blockCaller early traps).targets := by
  cases early <;> simp [blockCaller, Function.targets, codeTargets, Op.targets, returningBlock, blockHead, blockTail,
    skipped, readArg, add]

/-- These fixture paths step only from within a label until its final exit. -/
private inductive LabelTrace (step : Phase → Phase → Prop) : Phase → Phase → Prop where
  | refl (a : Phase) : LabelTrace step a a
  | tail {a b : Phase} {locals : List Value} {body : Body}
      (prior : LabelTrace step a (.label locals body)) (move : step (.label locals body) b) :
      LabelTrace step a b

private theorem labelTraceRun {early traps : Bool} {a b : Phase} (trace : LabelTrace (BlockLayer early traps) a b) :
    (blockGraph early traps).Runs (blockChecked early traps) ⟨1⟩ a b := by
  induction trace with
  | refl => exact .refl
  | tail _ move ih => exact ih.tail (blockEdge early traps move)

private theorem wrapBlock {early traps : Bool} {a b : Phase} (trace : LabelTrace (BlockLayer early traps) a b)
    (saved : List Value) (result : Option NumType) (rest : List Op) :
    LabelTrace (BlockLayer early traps) (a.afterBlock saved result rest) (b.afterBlock saved result rest) := by
  induction trace with
  | refl => exact .refl _
  | tail _ move ih => exact ih.tail (.blockStep saved result rest move)

private theorem callWithin (early traps : Bool) (rest : List Op) :
    LabelTrace (BlockLayer early traps) (.label input (.running [] (blockHead traps ++ rest)))
      (.label input (.active [] (blockTarget traps) (.invoke input) rest)) := by
  have get : BlockLayer early traps (.label input (.running [] (blockHead traps ++ rest)))
      (.label input (.running input (.call (blockTarget traps) :: rest))) :=
    .numeric (.get (i := ⟨0⟩) (stack := []) (v := i32 7) rfl)
  exact ((LabelTrace.refl _).tail get).tail (.dispatch input [] input (blockTarget traps) rest (blockUsed early traps) rfl)

private theorem withinChild (early traps : Bool) (rest : List Op) {a b : Phase} (live : a.Active)
    (step : (blockGraph early traps).Edge (blockChecked early traps) ⟨0⟩ a b) :
    BlockLayer early traps (.label input (.active [] (blockTarget traps) a rest))
      (.label input (Body.attach [] (blockTarget traps) rest b)) :=
  .child input [] (blockTarget traps) rest (blockUsed early traps) live step

private theorem calledNormally (early : Bool) (rest : List Op) :
    LabelTrace (BlockLayer early false) (.label input (.running [] (blockHead false ++ rest)))
      (.label input (.running input rest)) := by
  have enter := (callWithin early false rest).tail
    (withinChild early false rest (a := .invoke input) trivial (childEdge early false (.enter input rfl)))
  have loaded := enter.tail (withinChild early false rest (a := .label input (.running [] [readArg])) trivial
    (childEdge early false (.numeric (.get (i := ⟨0⟩) (stack := []) (v := i32 7) rfl))))
  have popped := loaded.tail (withinChild early false rest (a := .label input (.running input [])) trivial
    (childEdge early false (.leaveValues input input)))
  exact popped.tail (withinChild early false rest (a := .exit input (.values input)) trivial
    (childEdge early false (.leaveFrame input (.values input) rfl)))

private theorem calledTrap (early : Bool) (rest : List Op) :
    LabelTrace (BlockLayer early true) (.label input (.running [] (blockHead true ++ rest)))
      (.label input (.trapped [] rest)) := by
  have enter := (callWithin early true rest).tail
    (withinChild early true rest (a := .invoke input) trivial (childEdge early true (.enter input rfl)))
  have trapped := enter.tail (withinChild early true rest (a := .label input (.running [] [.unreachable])) trivial
    (childEdge early true (.unreachable input [] [])))
  have popped := trapped.tail (withinChild early true rest (a := .label input (.trapped [] [])) trivial
    (childEdge early true (.leaveTrap input)))
  exact popped.tail (withinChild early true rest (a := .exit input .trap) trivial
    (childEdge early true (.leaveFrame input .trap trivial)))

private theorem startBlockRoot (early traps : Bool) :
    (blockGraph early traps).Runs (blockChecked early traps) ⟨1⟩ (.call input)
      (.label input (.running blockSaved (blockCaller early traps).code)) :=
  (Relation.ReflTransGen.single (blockEdge early traps (.resolve input))).tail
    (blockEdge early traps (.enter input rfl))

private theorem fallthroughRun :
    (blockGraph false false).Runs (blockChecked false false) ⟨1⟩ (.call input) (.done (.values [i32 17])) := by
  have beginBlock := (startBlockRoot false false).tail
    (blockEdge false false (.blockEnter input blockSaved scalarBlock (blockHead false ++ blockTail) [add]))
  have get := (calledNormally false blockTail).tail (.numeric (.get (i := ⟨0⟩) (stack := input) (v := i32 7) rfl))
  have sum : Numerics.intBinOp .i32 .add 7 7 = .ok 14 := rfl
  have addValues := get.tail (.numeric (.bin (stack := []) sum))
  have fall := addValues.tail (.leaveValues input [i32 14])
  have after := beginBlock.trans (labelTraceRun (wrapBlock fall blockSaved scalarBlock [add]))
  have sum2 : Numerics.intBinOp .i32 .add 3 14 = .ok 17 := rfl
  have final := after.tail (blockEdge false false (.numeric (.bin (stack := []) sum2)))
  exact (final.tail (blockEdge false false (.leaveValues input [i32 17]))).tail
    (blockEdge false false (.leaveFrame input (.values [i32 17]) rfl))

private theorem explicitRun :
    (blockGraph true false).Runs (blockChecked true false) ⟨1⟩ (.call input) (.done (.values [i32 7])) := by
  have openOuter := (startBlockRoot true false).tail
    (blockEdge true false (.blockEnter input blockSaved none (returningBlock false) skipped))
  have openInner := openOuter.tail (blockEdge true false (.blockStep blockSaved none skipped
    (.blockEnter input [] wideBlock (blockHead false ++ .return_ :: skipped) skipped)))
  have returned := (calledNormally true (.return_ :: skipped)).tail (.returnLabel input input skipped)
  have crossOuter := (wrapBlock returned [] wideBlock skipped).tail (.returnLabel input input skipped)
  have after := openInner.trans (labelTraceRun (wrapBlock crossOuter blockSaved none skipped))
  have crossFunction := after.tail (blockEdge true false (.returnLabel input (blockSaved ++ input) skipped))
  exact crossFunction.tail (blockEdge true false (.returnFrame input blockSaved input rfl))

private theorem blockTrapRun :
    (blockGraph false true).Runs (blockChecked false true) ⟨1⟩ (.call input) (.done .trap) := by
  have beginBlock := (startBlockRoot false true).tail
    (blockEdge false true (.blockEnter input blockSaved scalarBlock (blockHead true ++ blockTail) [add]))
  have discardCode := (calledTrap false blockTail).tail (.discard (.cut [] [] blockTail [] (.inr (by simp [blockTail]))))
  have bubble := discardCode.tail (.leaveTrap input)
  have after := beginBlock.trans (labelTraceRun (wrapBlock bubble blockSaved scalarBlock [add]))
  have discardAll := after.tail (blockEdge false true (.discard (.cut [] blockSaved [add] [] (.inl (by simp [blockSaved])))))
  exact (discardAll.tail (blockEdge false true (.leaveTrap input))).tail
    (blockEdge false true (.leaveFrame input .trap trivial))

private theorem nestedTrapRun :
    (blockGraph true true).Runs (blockChecked true true) ⟨1⟩ (.call input) (.done .trap) := by
  have openOuter := (startBlockRoot true true).tail
    (blockEdge true true (.blockEnter input blockSaved none (returningBlock true) skipped))
  have openInner := openOuter.tail (blockEdge true true (.blockStep blockSaved none skipped
    (.blockEnter input [] wideBlock (blockHead true ++ .return_ :: skipped) skipped)))
  have discarded := (calledTrap true (.return_ :: skipped)).tail
    (.discard (.cut [] [] (Op.return_ :: skipped) [] (.inr (by simp))))
  have bubbled := wrapBlock (discarded.tail (.leaveTrap input)) [] wideBlock skipped
  have moved := bubbled.tail (.discard (.cut [] [] skipped [] (.inr (by simp [skipped]))))
  have after := openInner.trans (labelTraceRun (wrapBlock (moved.tail (.leaveTrap input)) blockSaved none skipped))
  have discardAll := after.tail (blockEdge true true (.discard (.cut [] blockSaved skipped [] (.inl (by simp [blockSaved])))))
  exact (discardAll.tail (blockEdge true true (.leaveTrap input))).tail
    (blockEdge true true (.leaveFrame input .trap trivial))

private def blockRootTarget (early traps : Bool) : CallTarget := ⟨⟨0⟩, ⟨1⟩, (blockCaller early traps).declaration⟩

private theorem blockRoot (early traps : Bool) : Root (blockGraph early traps) (callerFrame ⟨1⟩)
    (blockRootTarget early traps) (blockCaller early traps) :=
  ⟨rfl, rfl, rfl⟩

private def blockResult (early traps : Bool) : Nested.Result :=
  if traps then .trap else .values [i32 (if early then 7 else 17)]

private theorem blockRun (early traps : Bool) :
    (blockGraph early traps).Runs (blockChecked early traps) ⟨1⟩ (.call input) (.done (blockResult early traps)) := by
  cases early <;> cases traps
  · exact fallthroughRun
  · exact blockTrapRun
  · exact explicitRun
  · exact nestedTrapRun

private theorem blockResultTyped (early traps : Bool) :
    Admitted (blockGraph early traps) (blockCaller early traps) (.done (blockResult early traps)) := by
  cases traps
  · exact .done rfl
  · exact .done trivial

example (early traps : Bool) : Execution.Core.Steps
    Numerics.Profile.spec SingleThreaded.Det.noHost
    (coreConfig (coreStore (blockGraph early traps)) (callerFrame ⟨1⟩) (blockRootTarget early traps) (.call input))
    (coreConfig (coreStore (blockGraph early traps)) (callerFrame ⟨1⟩) (blockRootTarget early traps)
      (.done (blockResult early traps))) :=
  (core_run_iff (blockChecked early traps) (coreAllocated _) (blockRoot early traps) (.call rfl)).mpr
    ⟨_, blockRun early traps, blockResultTyped early traps, rfl⟩

example (early traps : Bool) : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeConfig (limeStore (blockGraph early traps)) (callerFrame ⟨1⟩) (blockRootTarget early traps) (.call input))
    (limeConfig (limeStore (blockGraph early traps)) (callerFrame ⟨1⟩) (blockRootTarget early traps)
      (.done (blockResult early traps))) :=
  (lime_run_iff (blockChecked early traps) (limeAllocated _) (blockRoot early traps) (.call rfl)).mpr
    ⟨_, blockRun early traps, blockResultTyped early traps, rfl⟩

example (early traps : Bool) : V1.Execution.Steps CallFrame.v1NoHost
    (v1Config (v1Store (blockGraph early traps)) (callerFrame ⟨1⟩) (blockRootTarget early traps) (.call input))
    (v1Config (v1Store (blockGraph early traps)) (callerFrame ⟨1⟩) (blockRootTarget early traps)
      (.done (blockResult early traps))) :=
  (v1_run_iff (blockV1Checked early traps) (v1Allocated _) (blockRoot early traps) (.call rfl) rfl).mpr
    ⟨_, blockRun early traps, blockResultTyped early traps, rfl⟩


private def conditionValue (takeThen : Bool) : BitVec 32 := if takeThen then 1 else 0

private def thenArm (early traps : Bool) : List Op :=
  if early then skipped else blockHead traps

private def elseArm (early : Bool) : List Op :=
  if early then [.block none (readArg :: .return_ :: skipped)] ++ skipped else [readArg, readArg, add]

private def ifResultType (early : Bool) : Option NumType := if early then wideBlock else scalarBlock
private def ifRest (early : Bool) : List Op := if early then skipped else [add]

private def ifCaller (takeThen early traps : Bool) : Function :=
  ⟨declaration [⟨0⟩], 1, blockSaved ++ [i32 (conditionValue takeThen)],
    .if_ (ifResultType early) (thenArm early traps) (elseArm early) :: ifRest early⟩

private def ifGraph (takeThen early traps : Bool) : Program :=
  ⟨[some (leaf traps), some (ifCaller takeThen early traps)]⟩

private theorem ifChecked (takeThen early traps : Bool) : (ifGraph takeThen early traps).check = true := by
  cases takeThen <;> cases early <;> cases traps <;> rfl

private theorem ifV1Checked (takeThen early traps : Bool) : (ifGraph takeThen early traps).checkV1 = true := by
  cases takeThen <;> cases early <;> cases traps <;> rfl

-- Check even an untaken arm, including its stack and call rank.
example : ({ ifCaller true false false with
    code := [.if_ scalarBlock (thenArm false false) [], add] }).check = false := rfl

example : ({ ifCaller true false false with initial := blockSaved ++ [Value.int .i64 1] }).check = false := rfl

example : (Program.mk [some (leaf false), some
    { ifCaller false false false with rank := 0 }]).check = false := rfl

private abbrev IfLayer (takeThen early traps : Bool) :=
  Layer (ifCaller takeThen early traps)
    (fun target => (ifGraph takeThen early traps).Edge (ifChecked takeThen early traps) target.address)

private theorem ifEdge {takeThen early traps : Bool} {a b : Phase} (h : IfLayer takeThen early traps a b) :
    (ifGraph takeThen early traps).Edge (ifChecked takeThen early traps) ⟨1⟩ a b :=
  ((ifGraph takeThen early traps).edge_iff (ifChecked takeThen early traps)
    (fn := ifCaller takeThen early traps) rfl).mpr h

private def ifSource (takeThen early traps : Bool) : Phase :=
  .label input (.running (ifCaller takeThen early traps).initial (ifCaller takeThen early traps).code)

private def ifSelected (takeThen early traps : Bool) : Phase :=
  .label input (.running blockSaved (.block (ifResultType early)
    (if takeThen then thenArm early traps else elseArm early) :: ifRest early))

private theorem ifSelectEdge (takeThen early traps : Bool) :
    (ifGraph takeThen early traps).Edge (ifChecked takeThen early traps) ⟨1⟩
      (ifSource takeThen early traps) (ifSelected takeThen early traps) := by
  cases takeThen <;> exact ifEdge (.ifSelect input blockSaved (conditionValue _) (ifResultType early)
    (thenArm early traps) (elseArm early) (ifRest early))

private theorem ifStart (takeThen early traps : Bool) :
    (ifGraph takeThen early traps).Runs (ifChecked takeThen early traps) ⟨1⟩ (.call input)
      (.label input (.block blockSaved (ifResultType early)
        (.running [] (if takeThen then thenArm early traps else elseArm early)) (ifRest early))) := by
  have resolve := Relation.ReflTransGen.single
    (ifEdge (takeThen := takeThen) (early := early) (traps := traps) (.resolve input))
  have entered := resolve.tail (ifEdge (.enter input rfl))
  exact (entered.tail (ifSelectEdge takeThen early traps)).tail
    (ifEdge (.blockEnter input blockSaved (ifResultType early)
      (if takeThen then thenArm early traps else elseArm early) (ifRest early)))

private def armOutcome (traps : Bool) : Nested.Result := if traps then .trap else .values input

private theorem thenCall (traps : Bool) :
    (ifGraph true false traps).Runs (ifChecked true false traps) ⟨1⟩ (.call input)
      (.label input (.block blockSaved scalarBlock (.attach [] (blockTarget traps) [] (.done (armOutcome traps))) [add])) := by
  let p := ifGraph true false traps
  let checked := ifChecked true false traps
  have used : blockTarget traps ∈ (ifCaller true false traps).targets := by
    simp [Function.targets, ifCaller, thenArm, elseArm, blockHead, codeTargets, Op.targets]
  have get := (ifStart true false traps).tail
    (ifEdge (.blockStep blockSaved scalarBlock [add] (.numeric (.get (i := ⟨0⟩) (stack := []) (v := i32 7) rfl))))
  have atChild := get.tail (ifEdge (.blockStep blockSaved scalarBlock [add]
    (.dispatch input [] input (blockTarget traps) [] used rfl)))
  have child {a b : Phase} (move : Layer (leaf traps) (fun t => p.Edge checked t.address) a b) :
      p.Edge checked ⟨0⟩ a b :=
    (p.edge_iff checked (fn := leaf traps) rfl).mpr move
  have lift {a b : Phase} (live : a.Active) (move : p.Edge checked ⟨0⟩ a b) :
      p.Edge checked ⟨1⟩ (.label input (.block blockSaved scalarBlock (.active [] (blockTarget traps) a []) [add]))
        ((.label input (Body.attach [] (blockTarget traps) [] b) : Phase).afterBlock blockSaved scalarBlock [add]) :=
    ifEdge (.blockStep blockSaved scalarBlock [add] (.child input [] (blockTarget traps) [] used live move))
  have entered := atChild.tail (lift (a := .invoke input) trivial (child (.enter input rfl)))
  cases traps
  · have got := entered.tail (lift (a := .label input (.running [] [readArg])) trivial
      (child (.numeric (.get (i := ⟨0⟩) (stack := []) (v := i32 7) rfl))))
    have left := got.tail (lift (a := .label input (.running input [])) trivial (child (.leaveValues input input)))
    exact left.tail (lift (a := .exit input (.values input)) trivial (child (.leaveFrame input (.values input) rfl)))
  · have trapped := entered.tail (lift (a := .label input (.running [] skipped)) trivial
      (child (.unreachable input [] [])))
    have left := trapped.tail (lift (a := .label input (.trapped [] [])) trivial (child (.leaveTrap input)))
    exact left.tail (lift (a := .exit input .trap) trivial (child (.leaveFrame input .trap trivial)))

private theorem ifFinish {takeThen : Bool} {v answer : BitVec 32}
    (run : (ifGraph takeThen false false).Runs (ifChecked takeThen false false) ⟨1⟩ (.call input)
      (.label input (.block blockSaved scalarBlock (.running [i32 v] []) [add])))
    (sum : Numerics.intBinOp .i32 .add 3 v = .ok answer) :
    (ifGraph takeThen false false).Runs (ifChecked takeThen false false) ⟨1⟩ (.call input) (.done (.values [i32 answer])) := by
  have resumed := run.tail (ifEdge (.blockStep blockSaved scalarBlock [add] (.leaveValues input [i32 v])))
  have added := resumed.tail (ifEdge (.numeric (.bin (stack := []) sum)))
  exact (added.tail (ifEdge (.leaveValues input [i32 answer]))).tail
    (ifEdge (.leaveFrame input (.values [i32 answer]) rfl))

private theorem ifThenRun :
    (ifGraph true false false).Runs (ifChecked true false false) ⟨1⟩ (.call input) (.done (.values [i32 10])) :=
  ifFinish (thenCall false) rfl

private theorem ifElseRun :
    (ifGraph false false false).Runs (ifChecked false false false) ⟨1⟩ (.call input) (.done (.values [i32 17])) := by
  have get := (ifStart false false false).tail (ifEdge (.blockStep blockSaved scalarBlock [add]
    (.numeric (.get (i := ⟨0⟩) (stack := []) (v := i32 7) rfl))))
  have getAgain := get.tail (ifEdge (.blockStep blockSaved scalarBlock [add]
    (.numeric (.get (i := ⟨0⟩) (stack := input) (v := i32 7) rfl))))
  have sum : Numerics.intBinOp .i32 .add 7 7 = .ok 14 := rfl
  exact ifFinish (getAgain.tail (ifEdge (.blockStep blockSaved scalarBlock [add] (.numeric (.bin (stack := []) sum))))) rfl

private theorem ifReturnRun :
    (ifGraph false true false).Runs (ifChecked false true false) ⟨1⟩ (.call input) (.done (.values input)) := by
  have enter := (ifStart false true false).tail (ifEdge (.blockStep blockSaved wideBlock skipped
    (.blockEnter input [] none (readArg :: .return_ :: skipped) skipped)))
  have get := enter.tail (ifEdge (.blockStep blockSaved wideBlock skipped (.blockStep [] none skipped
    (.numeric (.get (i := ⟨0⟩) (stack := []) (v := i32 7) rfl)))))
  have crossInner := get.tail (ifEdge (.blockStep blockSaved wideBlock skipped (.blockStep [] none skipped
    (.returnLabel input input skipped))))
  have crossArm := crossInner.tail (ifEdge (.blockStep blockSaved wideBlock skipped (.returnLabel input input skipped)))
  have crossFunction := crossArm.tail (ifEdge (.returnLabel input (blockSaved ++ input) skipped))
  exact crossFunction.tail (ifEdge (.returnFrame input blockSaved input rfl))

private theorem ifTrapRun :
    (ifGraph true false true).Runs (ifChecked true false true) ⟨1⟩ (.call input) (.done .trap) := by
  have propagate := (thenCall true).tail (ifEdge (.blockStep blockSaved scalarBlock [add] (.leaveTrap input)))
  have discard := propagate.tail (ifEdge (.discard (.cut [] blockSaved [add] [] (.inl (by simp [blockSaved])))))
  exact (discard.tail (ifEdge (.leaveTrap input))).tail (ifEdge (.leaveFrame input .trap trivial))

private def ifRootTarget (takeThen early traps : Bool) : CallTarget :=
  ⟨⟨0⟩, ⟨1⟩, (ifCaller takeThen early traps).declaration⟩

private theorem ifRoot (takeThen early traps : Bool) : Root (ifGraph takeThen early traps) (callerFrame ⟨1⟩)
    (ifRootTarget takeThen early traps) (ifCaller takeThen early traps) :=
  ⟨rfl, rfl, rfl⟩

private theorem ifNative {takeThen early traps : Bool} {result : Nested.Result}
    (run : (ifGraph takeThen early traps).Runs (ifChecked takeThen early traps) ⟨1⟩ (.call input) (.done result)) :
    let p := ifGraph takeThen early traps
    let caller := callerFrame ⟨1⟩
    let target := ifRootTarget takeThen early traps
    Execution.Core.Steps Numerics.Profile.spec SingleThreaded.Det.noHost
      (coreConfig (coreStore p) caller target (.call input)) (coreConfig (coreStore p) caller target (.done result)) ∧
    Lime1.Execution.Steps CallFrame.limeNoHost
      (limeConfig (limeStore p) caller target (.call input)) (limeConfig (limeStore p) caller target (.done result)) ∧
    V1.Execution.Steps CallFrame.v1NoHost
      (v1Config (v1Store p) caller target (.call input)) (v1Config (v1Store p) caller target (.done result)) := by
  have checked := ifChecked takeThen early traps
  have root := ifRoot takeThen early traps
  have ready : Admitted (ifGraph takeThen early traps) (ifCaller takeThen early traps) (.call input) := .call rfl
  have endpoint := Program.admitted_run checked root.found ready run
  exact ⟨(core_run_iff checked (coreAllocated _) root ready).mpr ⟨_, run, endpoint, rfl⟩,
    (lime_run_iff checked (limeAllocated _) root ready).mpr ⟨_, run, endpoint, rfl⟩,
    (v1_run_iff (ifV1Checked takeThen early traps) (v1Allocated _) root ready rfl).mpr ⟨_, run, endpoint, rfl⟩⟩

example := ifNative ifThenRun
example := ifNative ifElseRun
example := ifNative ifReturnRun
example := ifNative ifTrapRun


private def branchArgs : List Value := [i32 7, i32 99]
private def branchSaved : List Value := [i32 12]
private def branchSub : Op := .numeric (.bin .i32 .sub)
private def branchBody (depth : LabelIdx) : List Op :=
  [readSecond, readArg, .br depth [int32], .unreachable]
private def branchArm : List Op :=
  [readSecond, .block wideBlock (branchBody ⟨1⟩), .unreachable]

private def branchFn (nested : Bool) : Function :=
  ⟨{ declaration [] with params := [int32, int32] }, 0,
    if nested then branchSaved ++ [i32 1] else branchSaved,
    if nested then [.if_ scalarBlock branchArm [readArg], branchSub]
    else [.block scalarBlock (branchBody ⟨0⟩), branchSub]⟩

private def branchGraph (nested : Bool) : Program := ⟨[some (branchFn nested)]⟩

private theorem branchChecked (nested : Bool) : (branchGraph nested).check = true := by
  cases nested <;> rfl

private theorem branchV1Checked (nested : Bool) : (branchGraph nested).checkV1 = true := by
  cases nested <;> rfl

-- The target still takes an i32 when the crossed block requires i64 and the function returns nothing.
example : ({ branchFn true with
    declaration := { (branchFn true).declaration with results := [] }
    code := [.if_ scalarBlock branchArm [readArg], branchSub, .set ⟨1⟩] }).check = true := rfl

-- The payload cannot come from the saved prefix.
example : ({ branchFn false with code := [.block scalarBlock [.br ⟨0⟩ [int32]], branchSub] }).check =
    false := rfl

-- A target of the right arity still needs a payload of the declared type.
example : ({ branchFn false with
    code := [.block wideBlock [readArg, .br ⟨0⟩ [.int .i64]], .unreachable] }).check = false := rfl

-- The branch annotation must agree with the label's result.
example : ({ branchFn false with
    code := [.block scalarBlock [readArg, .br ⟨0⟩ []], branchSub] }).check = false := rfl

-- Depths past this activation's function label are out of range.
example : ({ branchFn false with code := [.block scalarBlock (branchBody ⟨2⟩), branchSub] }).check =
    false := rfl
example : ({ branchFn false with code := [.br ⟨1⟩ [int32]] }).check = false := rfl

private theorem branchEdge (nested : Bool) {a b : Phase}
    (step : Layer (branchFn nested) (fun t => (branchGraph nested).Edge (branchChecked nested) t.address) a b) :
    (branchGraph nested).Edge (branchChecked nested) ⟨0⟩ a b :=
  ((branchGraph nested).edge_iff (branchChecked nested) (fn := branchFn nested) rfl).mpr step

private abbrev BranchRun (nested : Bool) :=
  (branchGraph nested).Runs (branchChecked nested) ⟨0⟩ (.call branchArgs)

private theorem branchStart (nested : Bool) :
    BranchRun nested (.label branchArgs (.running (branchFn nested).initial (branchFn nested).code)) :=
  (Relation.ReflTransGen.single (branchEdge nested (.resolve branchArgs))).tail
    (branchEdge nested (.enter branchArgs rfl))

private def branchResumed : Phase :=
  .label branchArgs (.running (branchSaved ++ [i32 7]) [branchSub])

private theorem branchZeroResume : BranchRun false branchResumed := by
  have opened := (branchStart false).tail (branchEdge false
    (.blockEnter branchArgs branchSaved scalarBlock (branchBody ⟨0⟩) [branchSub]))
  have scratch := opened.tail (branchEdge false (.blockStep branchSaved scalarBlock [branchSub]
    (.numeric (.get (i := ⟨1⟩) (stack := []) (v := i32 99) rfl))))
  have payload := scratch.tail (branchEdge false (.blockStep branchSaved scalarBlock [branchSub]
    (.numeric (.get (i := ⟨0⟩) (stack := [i32 99]) (v := i32 7) rfl))))
  exact payload.tail (branchEdge false (.blockStep branchSaved scalarBlock [branchSub]
    (.branchHere branchArgs [i32 99] [i32 7] [int32] skipped rfl)))

private theorem branchCrossInner :
    BranchRun true (.label branchArgs (.block branchSaved scalarBlock
      (.running [i32 99, i32 99, i32 7] [.br ⟨0⟩ [int32], .unreachable]) [branchSub])) := by
  have selected := (branchStart true).tail (branchEdge true
    (.ifSelect branchArgs branchSaved 1 scalarBlock branchArm [readArg] [branchSub]))
  have opened := selected.tail (branchEdge true
    (.blockEnter branchArgs branchSaved scalarBlock branchArm [branchSub]))
  have outerScratch := opened.tail (branchEdge true (.blockStep branchSaved scalarBlock [branchSub]
    (.numeric (.get (i := ⟨1⟩) (stack := []) (v := i32 99) rfl))))
  have inner := outerScratch.tail (branchEdge true (.blockStep branchSaved scalarBlock [branchSub]
    (.blockEnter branchArgs [i32 99] wideBlock (branchBody ⟨1⟩) skipped)))
  have innerScratch := inner.tail (branchEdge true (.blockStep branchSaved scalarBlock [branchSub]
    (.blockStep [i32 99] wideBlock skipped (.numeric (.get (i := ⟨1⟩) (stack := []) (v := i32 99) rfl)))))
  have payload := innerScratch.tail (branchEdge true (.blockStep branchSaved scalarBlock [branchSub]
    (.blockStep [i32 99] wideBlock skipped (.numeric (.get (i := ⟨0⟩) (stack := [i32 99]) (v := i32 7) rfl)))))
  exact payload.tail (branchEdge true (.blockStep branchSaved scalarBlock [branchSub]
    (.blockStep [i32 99] wideBlock skipped
      (.branchOuter branchArgs [i32 99, i32 7] ⟨1⟩ [int32] skipped (by decide)))))

private theorem branchNestedResume : BranchRun true branchResumed :=
  branchCrossInner.tail (branchEdge true (.blockStep branchSaved scalarBlock [branchSub]
    (.branchHere branchArgs [i32 99, i32 99] [i32 7] [int32] skipped rfl)))

private theorem branchResume (nested : Bool) : BranchRun nested branchResumed := by
  cases nested
  · exact branchZeroResume
  · exact branchNestedResume

private theorem branchRun (nested : Bool) : BranchRun nested (.done (.values [i32 5])) := by
  have sub : Numerics.intBinOp .i32 .sub 12 7 = .ok 5 := rfl
  have evaluated := (branchResume nested).tail (branchEdge nested (.numeric (.bin (stack := []) sub)))
  exact (evaluated.tail (branchEdge nested (.leaveValues branchArgs [i32 5]))).tail
    (branchEdge nested (.leaveFrame branchArgs (.values [i32 5]) rfl))

private def branchRootTarget (nested : Bool) : CallTarget := ⟨⟨0⟩, ⟨0⟩, (branchFn nested).declaration⟩

private theorem branchRoot (nested : Bool) :
    Root (branchGraph nested) (callerFrame ⟨0⟩) (branchRootTarget nested) (branchFn nested) :=
  ⟨rfl, rfl, rfl⟩

private theorem nativeRun {program : Program} {caller : Execution.Runtime.Frame} {target : CallTarget}
    {fn : Function} {start out : Phase} (checked : program.check = true) (checkedV1 : program.checkV1 = true)
    (root : Root program caller target fn) (ready : Admitted program fn start)
    (run : program.Runs checked target.address start out) (supported : start.supportsV1 = true := by rfl) :
    Execution.Core.Steps Numerics.Profile.spec SingleThreaded.Det.noHost
      (coreConfig (coreStore program) caller target start) (coreConfig (coreStore program) caller target out) ∧
    Lime1.Execution.Steps CallFrame.limeNoHost
      (limeConfig (limeStore program) caller target start) (limeConfig (limeStore program) caller target out) ∧
    V1.Execution.Steps CallFrame.v1NoHost
      (v1Config (v1Store program) caller target start) (v1Config (v1Store program) caller target out) := by
  have endpoint := Program.admitted_run checked root.found ready run
  exact ⟨(core_run_iff checked (coreAllocated _) root ready).mpr ⟨_, run, endpoint, rfl⟩,
    (lime_run_iff checked (limeAllocated _) root ready).mpr ⟨_, run, endpoint, rfl⟩,
    (v1_run_iff checkedV1 (v1Allocated _) root ready supported).mpr ⟨_, run, endpoint, rfl⟩⟩

-- Check both the resumed operand order and the noncommutative continuation result.
example (nested : Bool) := nativeRun (branchChecked nested) (branchV1Checked nested) (branchRoot nested)
  (.call (args := branchArgs) rfl) (branchResume nested)
example (nested : Bool) := nativeRun (branchChecked nested) (branchV1Checked nested) (branchRoot nested)
  (.call (args := branchArgs) rfl) (branchRun nested)
example := nativeRun (branchChecked true) (branchV1Checked true) (branchRoot true)
  (.call (args := branchArgs) rfl) branchCrossInner

private def readBranchSelector : Op := .numeric (.get ⟨2⟩)
private def branchCaseSaved : List Value := [i32 200]
private def branchCaseArgs (condition : BitVec 32) : List Value := branchArgs ++ [i32 condition]
private def branchCaseOperands : List Value := [i32 99, i32 7]
private def branchCaseTail : List Op := [readArg, add]

private def branchCaseBody (op : Op) : List Op :=
  [readSecond, readArg, readBranchSelector, op, branchSub]

private def brIfBody (depth : LabelIdx) (result : List NumType) : List Op :=
  branchCaseBody (.brIf depth result)

private def branchCaseArm (body : List Op) : List Op := .block scalarBlock body :: branchCaseTail

private def branchCaseCode (body : List Op) : List Op :=
  [.if_ scalarBlock (branchCaseArm body) [readArg], branchSub]

private def brIfFn : Function :=
  ⟨{ declaration [] with params := [int32, int32, int32] }, 0, branchCaseSaved ++ [i32 1],
    branchCaseCode (brIfBody ⟨1⟩ [int32])⟩

private def brIfGraph : Program := ⟨[some brIfFn]⟩
private theorem brIfChecked : brIfGraph.check = true := rfl
private theorem brIfV1Checked : brIfGraph.checkV1 = true := rfl

-- The condition reads a default-zero local in these checks.
private def zeroConditionFn : Function :=
  { brIfFn with declaration := { brIfFn.declaration with params := [int32, int32], locals := [int32] } }

example : zeroConditionFn.check = true := rfl
example : ({ zeroConditionFn with code := branchCaseCode (brIfBody ⟨3⟩ [int32]) }).check = false := rfl
example : ({ zeroConditionFn with code := branchCaseCode (brIfBody ⟨1⟩ []) }).check = false := rfl
example : ({ zeroConditionFn with declaration := { zeroConditionFn.declaration with locals := [.int .i64] } }).check =
    false := rfl

-- Fallthrough could store the i64 scratch value, but the taken i32 branch cannot use it.
example : ({ zeroConditionFn with
    declaration := { zeroConditionFn.declaration with locals := [int32, .int .i64] }
    code := branchCaseCode [readSecond, readArg, .numeric (.get ⟨3⟩), readBranchSelector, .brIf ⟨1⟩ [int32],
      .set ⟨3⟩, branchSub] }).check = false := rfl

-- A well-typed taken path still needs a valid fallthrough.
example : ({ zeroConditionFn with code := branchCaseCode [readSecond, readArg, readBranchSelector, .brIf ⟨1⟩ [int32]] }).check =
    false := rfl

private abbrev BrIfLayer := Layer brIfFn (fun t => brIfGraph.Edge brIfChecked t.address)

private theorem brIfEdge {a b : Phase} (step : BrIfLayer a b) : brIfGraph.Edge brIfChecked ⟨0⟩ a b :=
  (brIfGraph.edge_iff brIfChecked (fn := brIfFn) rfl).mpr step

private abbrev BrIfRun (condition : BitVec 32) := brIfGraph.Runs brIfChecked ⟨0⟩ (.call (branchCaseArgs condition))

private def branchCaseInner (condition : BitVec 32) (stack : List Value) (rest : List Op) : Phase :=
  .label (branchCaseArgs condition) (.block branchCaseSaved scalarBlock
    (.block [] scalarBlock (.running stack rest) branchCaseTail) [branchSub])

private theorem brIfInnerStep {condition : BitVec 32} {stack : List Value} {rest : List Op} {next : Phase}
    (step : BrIfLayer (.label (branchCaseArgs condition) (.running stack rest)) next) :
    brIfGraph.Edge brIfChecked ⟨0⟩ (branchCaseInner condition stack rest)
      ((next.afterBlock [] scalarBlock branchCaseTail).afterBlock branchCaseSaved scalarBlock [branchSub]) :=
  brIfEdge (.blockStep branchCaseSaved scalarBlock [branchSub] (.blockStep [] scalarBlock branchCaseTail step))

private theorem brIfFromCall (condition : BitVec 32) :
    BrIfRun condition (branchCaseInner condition (branchCaseOperands ++ [i32 condition]) [.brIf ⟨1⟩ [int32], branchSub]) := by
  let args := branchCaseArgs condition
  let body := brIfBody ⟨1⟩ [int32]
  have entered := (Relation.ReflTransGen.single (brIfEdge (.resolve args))).tail (brIfEdge (.enter args rfl))
  have selected := entered.tail (brIfEdge (.ifSelect args branchCaseSaved 1 scalarBlock (branchCaseArm body) [readArg] [branchSub]))
  have outer := selected.tail (brIfEdge (.blockEnter args branchCaseSaved scalarBlock (branchCaseArm body) [branchSub]))
  have inner := outer.tail (brIfEdge (.blockStep branchCaseSaved scalarBlock [branchSub]
    (.blockEnter args [] scalarBlock body branchCaseTail)))
  have scratch := inner.tail (brIfInnerStep (condition := condition)
    (.numeric (.get (i := ⟨1⟩) (stack := []) (v := i32 99) rfl)))
  have payload := scratch.tail (brIfInnerStep (condition := condition)
    (.numeric (.get (i := ⟨0⟩) (stack := [i32 99]) (v := i32 7) rfl)))
  exact payload.tail (brIfInnerStep (condition := condition)
    (.numeric (.get (i := ⟨2⟩) (stack := branchCaseOperands) (v := i32 condition) rfl)))

private theorem brIfSelectStep (condition : BitVec 32) :
    brIfGraph.Edge brIfChecked ⟨0⟩
      (branchCaseInner condition (branchCaseOperands ++ [i32 condition]) [.brIf ⟨1⟩ [int32], branchSub])
      (branchCaseInner condition branchCaseOperands (if condition = 0 then [branchSub] else [.br ⟨1⟩ [int32], branchSub])) :=
  brIfInnerStep (.branchIf (branchCaseArgs condition) branchCaseOperands condition ⟨1⟩ [int32] [branchSub])

private def branchCaseResumed (condition result : BitVec 32) : Phase :=
  .label (branchCaseArgs condition) (.running (branchCaseSaved ++ [i32 result]) [branchSub])

private theorem brIfTaken {condition : BitVec 32} (nonzero : condition ≠ 0) :
    BrIfRun condition (branchCaseResumed condition 7) := by
  have choose := brIfSelectStep condition
  rw [ite_eq_right nonzero] at choose
  have pending := (brIfFromCall condition).tail choose
  have cross := pending.tail (brIfInnerStep (.branchOuter (branchCaseArgs condition) branchCaseOperands ⟨1⟩
    [int32] [branchSub] (by decide)))
  exact cross.tail (brIfEdge (.blockStep branchCaseSaved scalarBlock [branchSub]
    (.branchHere (branchCaseArgs condition) [i32 99] [i32 7] [int32] branchCaseTail rfl)))

private theorem brIfFallsThrough : BrIfRun 0 (branchCaseResumed 0 99) := by
  have kept : BrIfRun 0 (branchCaseInner 0 branchCaseOperands [branchSub]) :=
    (brIfFromCall 0).tail (brIfSelectStep 0)
  have innerSub : Numerics.intBinOp .i32 .sub 99 7 = .ok 92 := rfl
  have difference := kept.tail (brIfInnerStep (.numeric (.bin (stack := []) innerSub)))
  have delivered := difference.tail (brIfInnerStep (.leaveValues (branchCaseArgs 0) [i32 92]))
  have get := delivered.tail (brIfEdge (.blockStep branchCaseSaved scalarBlock [branchSub]
    (.numeric (.get (i := ⟨0⟩) (stack := [i32 92]) (v := i32 7) rfl))))
  have outerAdd : Numerics.intBinOp .i32 .add 92 7 = .ok 99 := rfl
  have sum := get.tail (brIfEdge (.blockStep branchCaseSaved scalarBlock [branchSub]
    (.numeric (.bin (stack := []) outerAdd))))
  exact sum.tail (brIfEdge (.blockStep branchCaseSaved scalarBlock [branchSub] (.leaveValues (branchCaseArgs 0) [i32 99])))

private theorem brIfFinish {condition result answer : BitVec 32}
    (run : BrIfRun condition (branchCaseResumed condition result))
    (sub : Numerics.intBinOp .i32 .sub 200 result = .ok answer) :
    BrIfRun condition (.done (.values [i32 answer])) := by
  have evaluated := run.tail (brIfEdge (.numeric (.bin (stack := []) sub)))
  exact (evaluated.tail (brIfEdge (.leaveValues (branchCaseArgs condition) [i32 answer]))).tail
    (brIfEdge (.leaveFrame (branchCaseArgs condition) (.values [i32 answer]) rfl))

private def brIfRootTarget : CallTarget := ⟨⟨0⟩, ⟨0⟩, brIfFn.declaration⟩

private theorem brIfRoot : Root brIfGraph (callerFrame ⟨0⟩) brIfRootTarget brIfFn :=
  ⟨rfl, rfl, rfl⟩

example := nativeRun brIfChecked brIfV1Checked brIfRoot (.call (args := branchCaseArgs 0) rfl)
  ((brIfFromCall 0).tail (brIfSelectStep 0))
example := nativeRun brIfChecked brIfV1Checked brIfRoot (.call (args := branchCaseArgs 2) rfl)
  ((brIfFromCall 2).tail (brIfSelectStep 2))

example := nativeRun brIfChecked brIfV1Checked brIfRoot (.call (args := branchCaseArgs 0) rfl)
  (brIfFinish brIfFallsThrough (answer := 101) rfl)
example := nativeRun brIfChecked brIfV1Checked brIfRoot (.call (args := branchCaseArgs 2) rfl)
  (brIfFinish (brIfTaken (condition := 2) (by decide)) (answer := 193) rfl)


private def tableDepths (empty : Bool) : List LabelIdx := if empty then [] else [⟨0⟩]

private def brTableBody (depths : List LabelIdx) (fallback : LabelIdx) : List Op :=
  branchCaseBody (.brTable depths fallback [int32])

private def brTableFn (empty : Bool) : Function :=
  { brIfFn with code := branchCaseCode (brTableBody (tableDepths empty) ⟨1⟩) }

private def brTableGraph (empty : Bool) : Program := ⟨[some (brTableFn empty)]⟩

private theorem brTableChecked (empty : Bool) : (brTableGraph empty).check = true := by
  cases empty <;> rfl

private theorem brTableV1Checked (empty : Bool) : (brTableGraph empty).checkV1 = true := by
  cases empty <;> rfl

-- This selector reads a default-zero local, so slot zero would be selected.
private def zeroSelectorFn : Function :=
  { brTableFn false with declaration := zeroConditionFn.declaration }

example : zeroSelectorFn.check = true := rfl
example : ({ zeroSelectorFn with code := branchCaseCode (brTableBody [⟨0⟩, ⟨3⟩] ⟨1⟩) }).check = false := rfl
example : ({ zeroSelectorFn with code := branchCaseCode (brTableBody [⟨0⟩] ⟨3⟩) }).check = false := rfl
example : ({ zeroSelectorFn with declaration := { zeroSelectorFn.declaration with locals := [.int .i64] } }).check =
    false := rfl
example : ({ zeroSelectorFn with
    declaration := { zeroSelectorFn.declaration with locals := [int32, .int .i64] }
    code := branchCaseCode [.numeric (.get ⟨3⟩), readBranchSelector, .brTable [⟨0⟩] ⟨1⟩ [int32]] }).check =
    false := rfl

-- Slot zero selects the i32 conditional label. Depth zero is an i64 block label.
example : ({ zeroSelectorFn with
    code := [.if_ scalarBlock [.block wideBlock (brTableBody [⟨1⟩] ⟨1⟩), .unreachable] [readArg], branchSub] }).check =
    true := rfl
example : ({ zeroSelectorFn with
    code := [.if_ scalarBlock [.block wideBlock (brTableBody [⟨1⟩] ⟨0⟩), .unreachable] [readArg], branchSub] }).check =
    false := rfl

private abbrev BrTableLayer (empty : Bool) :=
  Layer (brTableFn empty) (fun t => (brTableGraph empty).Edge (brTableChecked empty) t.address)

private theorem brTableEdge (empty : Bool) {a b : Phase} (step : BrTableLayer empty a b) :
    (brTableGraph empty).Edge (brTableChecked empty) ⟨0⟩ a b :=
  ((brTableGraph empty).edge_iff (brTableChecked empty) (fn := brTableFn empty) rfl).mpr step

private abbrev BrTableRun (empty : Bool) (selector : BitVec 32) :=
  (brTableGraph empty).Runs (brTableChecked empty) ⟨0⟩ (.call (branchCaseArgs selector))

private theorem brTableInnerStep {empty : Bool} {selector : BitVec 32}
    {stack : List Value} {rest : List Op} {next : Phase}
    (step : BrTableLayer empty (.label (branchCaseArgs selector) (.running stack rest)) next) :
    (brTableGraph empty).Edge (brTableChecked empty) ⟨0⟩ (branchCaseInner selector stack rest)
      ((next.afterBlock [] scalarBlock branchCaseTail).afterBlock branchCaseSaved scalarBlock [branchSub]) :=
  brTableEdge empty (.blockStep branchCaseSaved scalarBlock [branchSub] (.blockStep [] scalarBlock branchCaseTail step))

private theorem brTableSelected (empty : Bool) (selector : BitVec 32) :
    BrTableRun empty selector (branchCaseInner selector branchCaseOperands
      [.br ((tableDepths empty)[selector.toNat]?.getD ⟨1⟩) [int32], branchSub]) := by
  let args := branchCaseArgs selector
  let body := brTableBody (tableDepths empty) ⟨1⟩
  have entered := (Relation.ReflTransGen.single (brTableEdge empty (.resolve args))).tail
    (brTableEdge empty (.enter args rfl))
  have chosenArm := entered.tail (brTableEdge empty
    (.ifSelect args branchCaseSaved 1 scalarBlock (branchCaseArm body) [readArg] [branchSub]))
  have outer := chosenArm.tail (brTableEdge empty
    (.blockEnter args branchCaseSaved scalarBlock (branchCaseArm body) [branchSub]))
  have inner := outer.tail (brTableEdge empty (.blockStep branchCaseSaved scalarBlock [branchSub]
    (.blockEnter args [] scalarBlock body branchCaseTail)))
  have scratch := inner.tail (brTableInnerStep (selector := selector)
    (.numeric (.get (i := ⟨1⟩) (stack := []) (v := i32 99) rfl)))
  have payload := scratch.tail (brTableInnerStep (selector := selector)
    (.numeric (.get (i := ⟨0⟩) (stack := [i32 99]) (v := i32 7) rfl)))
  have indexed := payload.tail (brTableInnerStep (selector := selector)
    (.numeric (.get (i := ⟨2⟩) (stack := branchCaseOperands) (v := i32 selector) rfl)))
  exact indexed.tail (brTableInnerStep
    (.branchTable args branchCaseOperands selector (tableDepths empty) ⟨1⟩ [int32] [branchSub]))

private theorem brTableHit : BrTableRun false 0 (branchCaseResumed 0 14) := by
  have chosen : BrTableRun false 0 (branchCaseInner 0 branchCaseOperands [.br ⟨0⟩ [int32], branchSub]) :=
    brTableSelected false 0
  have innerExit := chosen.tail (brTableInnerStep
    (.branchHere (branchCaseArgs 0) [i32 99] [i32 7] [int32] [branchSub] rfl))
  have addedArg := innerExit.tail (brTableEdge false (.blockStep branchCaseSaved scalarBlock [branchSub]
    (.numeric (.get (i := ⟨0⟩) (stack := [i32 7]) (v := i32 7) rfl))))
  have addValues : Numerics.intBinOp .i32 .add 7 7 = .ok 14 := rfl
  have sum := addedArg.tail (brTableEdge false (.blockStep branchCaseSaved scalarBlock [branchSub]
    (.numeric (.bin (stack := []) addValues))))
  exact sum.tail (brTableEdge false (.blockStep branchCaseSaved scalarBlock [branchSub]
    (.leaveValues (branchCaseArgs 0) [i32 14])))

private theorem brTableDefault (empty : Bool) (selector : BitVec 32)
    (miss : (tableDepths empty)[selector.toNat]? = none) :
    BrTableRun empty selector (branchCaseResumed selector 7) := by
  have chosen := brTableSelected empty selector
  rw [miss] at chosen
  have cross := chosen.tail (brTableInnerStep (.branchOuter (branchCaseArgs selector) branchCaseOperands ⟨1⟩
    [int32] [branchSub] (by decide)))
  exact cross.tail (brTableEdge empty (.blockStep branchCaseSaved scalarBlock [branchSub]
    (.branchHere (branchCaseArgs selector) [i32 99] [i32 7] [int32] branchCaseTail rfl)))

private theorem brTableFinish {empty : Bool} {selector result answer : BitVec 32}
    (run : BrTableRun empty selector (branchCaseResumed selector result))
    (sub : Numerics.intBinOp .i32 .sub 200 result = .ok answer) :
    BrTableRun empty selector (.done (.values [i32 answer])) := by
  have evaluated := run.tail (brTableEdge empty (.numeric (.bin (stack := []) sub)))
  exact (evaluated.tail (brTableEdge empty (.leaveValues (branchCaseArgs selector) [i32 answer]))).tail
    (brTableEdge empty (.leaveFrame (branchCaseArgs selector) (.values [i32 answer]) rfl))

private def brTableRootTarget (empty : Bool) : CallTarget := ⟨⟨0⟩, ⟨0⟩, (brTableFn empty).declaration⟩

private theorem brTableRoot (empty : Bool) :
    Root (brTableGraph empty) (callerFrame ⟨0⟩) (brTableRootTarget empty) (brTableFn empty) :=
  ⟨rfl, rfl, rfl⟩

example := nativeRun (brTableChecked false) (brTableV1Checked false) (brTableRoot false)
  (.call (args := branchCaseArgs 0) rfl) (brTableSelected false 0)
example := nativeRun (brTableChecked false) (brTableV1Checked false) (brTableRoot false)
  (.call (args := branchCaseArgs 0) rfl) (brTableFinish brTableHit (answer := 186) rfl)
example := nativeRun (brTableChecked false) (brTableV1Checked false) (brTableRoot false)
  (.call (args := branchCaseArgs 1) rfl) (brTableFinish (brTableDefault false 1 rfl) (answer := 193) rfl)
example := nativeRun (brTableChecked false) (brTableV1Checked false) (brTableRoot false)
  (.call (args := branchCaseArgs 0xFFFFFFFF) rfl)
  (brTableFinish (brTableDefault false 0xFFFFFFFF rfl) (answer := 193) rfl)
example := nativeRun (brTableChecked true) (brTableV1Checked true) (brTableRoot true)
  (.call (args := branchCaseArgs 0) rfl) (brTableFinish (brTableDefault true 0 rfl) (answer := 193) rfl)


private def functionLabelPayload (mixed : Bool) : List Value :=
  if mixed then [Value.int .i64 42, i32 7] else [i32 7]

private def directFunctionBranch (mixed : Bool) : Function :=
  let payload := functionLabelPayload mixed
  let results := payload.map Value.type
  ⟨{ declaration [] with params := [], results := results }, 0,
    [i32 99] ++ payload, [.br ⟨0⟩ results, .unreachable]⟩

private def directFunctionGraph (mixed : Bool) : Program := ⟨[some (directFunctionBranch mixed)]⟩

private theorem directFunctionChecked (mixed : Bool) : (directFunctionGraph mixed).check = true := by
  cases mixed <;> rfl

example : (directFunctionGraph false).checkV1 = true := rfl
example : (directFunctionGraph true).checkV1 = false := rfl

example : ({ directFunctionBranch true with initial := [i32 99, i32 7, Value.int .i64 42] }).check = false := rfl
example : ({ directFunctionBranch false with initial := [] }).check = false := rfl
example : ({ directFunctionBranch false with
    initial := [i32 0], code := [.brIf ⟨0⟩ [int32], .unreachable] }).check = false := rfl
example : ({ directFunctionBranch false with
    initial := [i32 7, i32 0], code := [.brTable [⟨0⟩] ⟨1⟩ [int32]] }).check = false := rfl

private theorem directFunctionEdge (mixed : Bool) {a b : Phase}
    (step : Layer (directFunctionBranch mixed)
      (fun t => (directFunctionGraph mixed).Edge (directFunctionChecked mixed) t.address) a b) :
    (directFunctionGraph mixed).Edge (directFunctionChecked mixed) ⟨0⟩ a b :=
  ((directFunctionGraph mixed).edge_iff (directFunctionChecked mixed) (fn := directFunctionBranch mixed) rfl).mpr step

private theorem directFunctionExit (mixed : Bool) :
    (directFunctionGraph mixed).Runs (directFunctionChecked mixed) ⟨0⟩ (.call [])
      (.exit [] (.values (functionLabelPayload mixed))) := by
  let payload := functionLabelPayload mixed
  have entered := (Relation.ReflTransGen.single (directFunctionEdge mixed (.resolve []))).tail
    (directFunctionEdge mixed (.enter [] rfl))
  exact entered.tail (directFunctionEdge mixed
    (.branchHere (kind := .exit) [] [i32 99] payload (payload.map Value.type) skipped (by simp)))

private theorem directFunctionRun (mixed : Bool) :
    (directFunctionGraph mixed).Runs (directFunctionChecked mixed) ⟨0⟩ (.call [])
      (.done (.values (functionLabelPayload mixed))) :=
  (directFunctionExit mixed).tail (directFunctionEdge mixed (.leaveFrame [] (.values (functionLabelPayload mixed)) rfl))

private def directFunctionTarget (mixed : Bool) : CallTarget := ⟨⟨0⟩, ⟨0⟩, (directFunctionBranch mixed).declaration⟩

private theorem directFunctionRoot (mixed : Bool) :
    Root (directFunctionGraph mixed) (callerFrame ⟨0⟩) (directFunctionTarget mixed) (directFunctionBranch mixed) :=
  ⟨rfl, rfl, rfl⟩

example (mixed : Bool) : Execution.Core.Steps Numerics.Profile.spec SingleThreaded.Det.noHost
    (coreConfig (coreStore (directFunctionGraph mixed)) (callerFrame ⟨0⟩) (directFunctionTarget mixed) (.call []))
    (coreConfig (coreStore (directFunctionGraph mixed)) (callerFrame ⟨0⟩) (directFunctionTarget mixed)
      (.done (.values (functionLabelPayload mixed)))) :=
  (core_run_iff (directFunctionChecked mixed) (coreAllocated _) (directFunctionRoot mixed) (.call rfl)).mpr
    ⟨_, directFunctionRun mixed, .done rfl, rfl⟩

example (mixed : Bool) : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeConfig (limeStore (directFunctionGraph mixed)) (callerFrame ⟨0⟩) (directFunctionTarget mixed) (.call []))
    (limeConfig (limeStore (directFunctionGraph mixed)) (callerFrame ⟨0⟩) (directFunctionTarget mixed)
      (.done (.values (functionLabelPayload mixed)))) :=
  (lime_run_iff (directFunctionChecked mixed) (limeAllocated _) (directFunctionRoot mixed) (.call rfl)).mpr
    ⟨_, directFunctionRun mixed, .done rfl, rfl⟩

example := nativeRun (directFunctionChecked false) rfl (directFunctionRoot false)
  (.call (args := []) rfl) (directFunctionRun false)

private def functionBranchTail : List Op := [.set ⟨0⟩]
private def functionBranchBody (table : Bool) : List Op :=
  [readArg, readArg, if table then .brTable [⟨1⟩] ⟨1⟩ [int32] else .brIf ⟨1⟩ [int32]] ++ functionBranchTail

private def functionBranchLeaf (table : Bool) : Function :=
  ⟨declaration [], 0, [i32 99], [.block none (functionBranchBody table), .return_]⟩

private def functionBranchChild (table : Bool) : CallTarget := ⟨⟨0⟩, ⟨0⟩, (functionBranchLeaf table).declaration⟩

private def functionBranchCaller (table : Bool) : Function :=
  ⟨declaration [⟨0⟩], 1, branchSaved, [readArg, .call (functionBranchChild table), branchSub]⟩

private def functionBranchGraph (table : Bool) : Program :=
  ⟨[some (functionBranchLeaf table), some (functionBranchCaller table)]⟩

private theorem functionBranchChecked (table : Bool) : (functionBranchGraph table).check = true := by
  cases table <;> rfl

private theorem functionBranchV1Checked (table : Bool) : (functionBranchGraph table).checkV1 = true := by
  cases table <;> rfl

-- The caller's block is active at the call site. The child's scope still ends at its own label.
private def callerWithBlock : Function :=
  { functionBranchCaller false with
    initial := []
    code := [.block scalarBlock [readArg, .call (functionBranchChild false)]] }

example : (Program.mk [some (functionBranchLeaf false), some callerWithBlock]).check = true := rfl
example : (Program.mk [some { functionBranchLeaf false with code := [.br ⟨1⟩ [int32]] }, some callerWithBlock]).check =
    false := rfl

private theorem functionBranchLeafEdge (table : Bool) {a b : Phase}
    (step : Layer (functionBranchLeaf table)
      (fun t => (functionBranchGraph table).Edge (functionBranchChecked table) t.address) a b) :
    (functionBranchGraph table).Edge (functionBranchChecked table) ⟨0⟩ a b :=
  ((functionBranchGraph table).edge_iff (functionBranchChecked table) (fn := functionBranchLeaf table) rfl).mpr step

private theorem functionBranchChildRun (table : Bool) :
    (functionBranchGraph table).Runs (functionBranchChecked table) ⟨0⟩ (.invoke input) (.done (.values input)) := by
  let saved := [i32 99]
  let rest : List Op := [.return_]
  have entered := Relation.ReflTransGen.single (functionBranchLeafEdge table (.enter input rfl))
  have opened := entered.tail (functionBranchLeafEdge table (.blockEnter input saved none (functionBranchBody table) rest))
  have operand := opened.tail (functionBranchLeafEdge table (.blockStep saved none rest
    (.numeric (.get (i := ⟨0⟩) (stack := []) (v := i32 7) rfl))))
  have selector := operand.tail (functionBranchLeafEdge table (.blockStep saved none rest
    (.numeric (.get (i := ⟨0⟩) (stack := input) (v := i32 7) rfl))))
  have selected : (functionBranchGraph table).Runs (functionBranchChecked table) ⟨0⟩ (.invoke input)
      (.label input (.block saved none (.running input (.br ⟨1⟩ [int32] :: functionBranchTail)) rest)) := by
    cases table
    · exact selector.tail (functionBranchLeafEdge false (.blockStep saved none rest
        (.branchIf input input 7 ⟨1⟩ [int32] functionBranchTail)))
    · exact selector.tail (functionBranchLeafEdge true (.blockStep saved none rest
        (.branchTable input input 7 [⟨1⟩] ⟨1⟩ [int32] functionBranchTail)))
  have atFunction := selected.tail (functionBranchLeafEdge table (.blockStep saved none rest
    (.branchOuter input input ⟨1⟩ [int32] functionBranchTail (by decide))))
  have exited := atFunction.tail (functionBranchLeafEdge table (.branchHere input saved input [int32] rest rfl))
  exact exited.tail (functionBranchLeafEdge table (.leaveFrame input (.values input) rfl))

private abbrev FunctionBranchRun (table : Bool) :=
  (functionBranchGraph table).Runs (functionBranchChecked table) ⟨1⟩ (.call input)

private theorem functionBranchCallerEdge (table : Bool) {a b : Phase}
    (step : Layer (functionBranchCaller table)
      (fun t => (functionBranchGraph table).Edge (functionBranchChecked table) t.address) a b) :
    (functionBranchGraph table).Edge (functionBranchChecked table) ⟨1⟩ a b :=
  ((functionBranchGraph table).edge_iff (functionBranchChecked table) (fn := functionBranchCaller table) rfl).mpr step

private theorem functionBranchResumes (table : Bool) :
    FunctionBranchRun table (.label input (.running (branchSaved ++ input) [branchSub])) := by
  let child := functionBranchChild table
  have used : child ∈ (functionBranchCaller table).targets := by
    simp [child, functionBranchCaller, Function.targets, codeTargets, Op.targets, readArg, branchSub]
  have entered := (Relation.ReflTransGen.single (functionBranchCallerEdge table (.resolve input))).tail
    (functionBranchCallerEdge table (.enter input rfl))
  have loaded := entered.tail (functionBranchCallerEdge table
    (.numeric (.get (i := ⟨0⟩) (stack := branchSaved) (v := i32 7) rfl)))
  exact loaded.trans ((functionBranchGraph table).compose_call (functionBranchChecked table)
    (fn := functionBranchCaller table) rfl used rfl (functionBranchChildRun table))

private theorem functionBranchRun (table : Bool) : FunctionBranchRun table (.done (.values [i32 5])) := by
  have sub : Numerics.intBinOp .i32 .sub 12 7 = .ok 5 := rfl
  have evaluated := (functionBranchResumes table).tail (functionBranchCallerEdge table (.numeric (.bin (stack := []) sub)))
  exact (evaluated.tail (functionBranchCallerEdge table (.leaveValues input [i32 5]))).tail
    (functionBranchCallerEdge table (.leaveFrame input (.values [i32 5]) rfl))

private def functionBranchRootTarget (table : Bool) : CallTarget :=
  ⟨⟨0⟩, ⟨1⟩, (functionBranchCaller table).declaration⟩

private theorem functionBranchRoot (table : Bool) :
    Root (functionBranchGraph table) (callerFrame ⟨1⟩) (functionBranchRootTarget table) (functionBranchCaller table) :=
  ⟨rfl, rfl, rfl⟩

example (table : Bool) := nativeRun (functionBranchChecked table) (functionBranchV1Checked table) (functionBranchRoot table)
  (.call (args := input) rfl) (functionBranchResumes table)
example (table : Bool) := nativeRun (functionBranchChecked table) (functionBranchV1Checked table) (functionBranchRoot table)
  (.call (args := input) rfl) (functionBranchRun table)

section ScalarLoops

private abbrev loopFlag : LocalIdx := ⟨0⟩
private abbrev loopValue : LocalIdx := ⟨1⟩
private abbrev loopZero : LocalIdx := ⟨2⟩
private abbrev loopDepth : LabelIdx := ⟨0⟩

private def readLocal (i : LocalIdx) : Op := .numeric (.get i)
private def onceBody : List Op :=
  [readLocal loopFlag, readLocal loopZero, .set loopFlag, .brIf loopDepth [], readLocal loopValue]

private def onceTail : List Op := [readLocal loopFlag, .numeric (.bin .i32 .sub)]
private def onceCode : List Op := .loop scalarBlock onceBody :: onceTail
private def onceArgs : List Value := [i32 1, i32 42]
private def onceLocals (flag : BitVec 32) : List Value := [i32 flag, i32 42, i32 0]

private def onceCallee : Function := ⟨⟨{}, ⟨0⟩, [int32, int32], [int32], [int32]⟩, 0, [], onceCode⟩
private def onceTarget : CallTarget := ⟨⟨0⟩, ⟨0⟩, onceCallee.declaration⟩
private def onceCaller : Function :=
  ⟨⟨{ funcs := [⟨0⟩] }, ⟨0⟩, [], [], [int32]⟩, 1, [i32 9] ++ onceArgs, [.call onceTarget, add]⟩
private def onceGraph : Program := ⟨[some onceCallee, some onceCaller]⟩
private def onceRootTarget : CallTarget := ⟨⟨0⟩, ⟨1⟩, onceCaller.declaration⟩

private theorem onceChecked : onceGraph.check = true := rfl
private theorem onceV1Checked : onceGraph.checkV1 = true := rfl
private theorem onceRoot : Root onceGraph (callerFrame ⟨1⟩) onceRootTarget onceCaller := ⟨rfl, rfl, rfl⟩

-- The loop's result type is separate from its empty branch payload.
example : ({ onceCallee with code := [.loop scalarBlock [.br loopDepth [int32]]] }).check = false := rfl
example : ({ onceCallee with code := [.loop scalarBlock []] }).check = false := rfl
example : ({ onceCallee with code := [.loop scalarBlock [readLocal loopValue, .br ⟨2⟩ [int32]]] }).check = false := rfl
example : ({ onceCallee with code := [.loop scalarBlock [.brIf loopDepth [], readLocal loopValue]] }).check = false := rfl

private theorem onceRule {a b : Phase}
    (step : Layer onceCallee (fun t => onceGraph.Edge onceChecked t.address) a b) :
    onceGraph.Edge onceChecked ⟨0⟩ a b :=
  (onceGraph.edge_iff onceChecked (fn := onceCallee) rfl).mpr step

private def inIteration (locals stack : List Value) (code : List Op) : Phase :=
  .label locals (.loop [] scalarBlock onceBody (.running stack code) onceTail)

private theorem iterationTest (flag : BitVec 32) :
    onceGraph.Runs onceChecked ⟨0⟩ (.label (onceLocals flag) (.running [] onceCode))
      (inIteration (onceLocals 0) [i32 flag] [.brIf loopDepth [], readLocal loopValue]) := by
  have enter := onceRule (.loopEnter (onceLocals flag) [] scalarBlock onceBody onceTail)
  have cached := onceRule (.loopStep [] scalarBlock onceBody onceTail
    (.numeric (locals := onceLocals flag) (rest := [readLocal loopZero, .set loopFlag, .brIf loopDepth [], readLocal loopValue])
      (.get (stack := []) (i := loopFlag) (v := i32 flag) rfl)))
  have zero := onceRule (.loopStep [] scalarBlock onceBody onceTail
    (.numeric (locals := onceLocals flag) (rest := [.set loopFlag, .brIf loopDepth [], readLocal loopValue])
      (.get (stack := [i32 flag]) (i := loopZero) (v := i32 0) rfl)))
  have set := onceRule (.loopStep [] scalarBlock onceBody onceTail
    (.localSet (saved := [i32 flag]) (rest := [.brIf loopDepth [], readLocal loopValue])
      (Locals.fact (.set (onceLocals flag) loopFlag (i32 0) (by change 0 < 3; decide)))))
  exact (((Relation.ReflTransGen.single enter).tail cached).tail zero).tail set

private theorem throughRestart :
    onceGraph.Runs onceChecked ⟨0⟩ (.invoke onceArgs)
      (.label (onceLocals 0) (.running [] onceCode)) := by
  have enter := onceRule (.enter onceArgs rfl)
  have taken := onceRule (.loopStep [] scalarBlock onceBody onceTail
    (.branchIf (onceLocals 0) [] 1 loopDepth [] [readLocal loopValue]))
  have restart := onceRule (.loopStep [] scalarBlock onceBody onceTail
    (.branchHere (onceLocals 0) [] [] [] [readLocal loopValue] rfl))
  exact (((Relation.ReflTransGen.single enter).trans (iterationTest 1)).tail taken).tail restart

private theorem onceReturns :
    onceGraph.Runs onceChecked ⟨0⟩ (.invoke onceArgs) (.done (.values [i32 42])) := by
  have skipped := (iterationTest 0).tail (onceRule (.loopStep [] scalarBlock onceBody onceTail
    (.branchIf (onceLocals 0) [] 0 loopDepth [] [readLocal loopValue])))
  have computed := skipped.tail (onceRule (.loopStep [] scalarBlock onceBody onceTail
    (.numeric (locals := onceLocals 0) (rest := []) (.get (stack := []) (i := loopValue) (v := i32 42) rfl))))
  have left := computed.tail (onceRule (.loopStep [] scalarBlock onceBody onceTail
    (.leaveValues (onceLocals 0) [i32 42])))
  have readUpdated := left.tail (onceRule (.numeric (locals := onceLocals 0) (rest := [.numeric (.bin .i32 .sub)])
    (.get (stack := [i32 42]) (i := loopFlag) (v := i32 0) rfl)))
  have subtracted := readUpdated.tail (onceRule (.numeric (rest := []) (.bin (stack := [])
    (show Numerics.intBinOp .i32 .sub 42 0 = .ok 42 from rfl))))
  have finish := (subtracted.tail (onceRule (.leaveValues (onceLocals 0) [i32 42]))).tail
    (onceRule (.leaveFrame (onceLocals 0) (.values [i32 42]) rfl))
  exact throughRestart.trans finish

private theorem onceCallerRuns :
    onceGraph.Runs onceChecked ⟨1⟩ (.call []) (.done (.values [i32 51])) := by
  have edge {a b : Phase} := (onceGraph.edge_iff onceChecked (address := ⟨1⟩) (fn := onceCaller)
    (a := a) (b := b) rfl).mpr
  have invoke := (Relation.ReflTransGen.single (edge (.resolve []))).tail (edge (.enter [] rfl))
  have child := Program.compose_call onceChecked (address := ⟨1⟩) (fn := onceCaller) (target := onceTarget)
    (locals := []) (saved := [i32 9]) (rest := [add]) rfl (by simp [onceCaller, Function.targets, codeTargets, Op.targets, add])
    rfl onceReturns
  have finish := (invoke.trans child).tail (edge (.numeric (rest := []) (.bin (stack := [])
    (show Numerics.intBinOp .i32 .add 9 42 = .ok 51 from rfl))))
  exact (finish.tail (edge (.leaveValues [] [i32 51]))).tail (edge (.leaveFrame [] (.values [i32 51]) rfl))

example := nativeRun onceChecked onceV1Checked onceRoot (.call (args := []) rfl) onceCallerRuns

private def foreverBody : List Op := [.br loopDepth []]
private def foreverCode : List Op := [.loop scalarBlock foreverBody]
private def foreverFn : Function := ⟨⟨{}, ⟨0⟩, [], [], [int32]⟩, 0, [], foreverCode⟩
private def foreverGraph : Program := ⟨[some foreverFn]⟩
private def foreverTarget : CallTarget := ⟨⟨0⟩, ⟨0⟩, foreverFn.declaration⟩
private theorem foreverV1Checked : foreverGraph.checkV1 = true := rfl
private theorem foreverChecked : foreverGraph.check = true := (Bool.and_eq_true_iff.mp foreverV1Checked).1
private theorem foreverRoot : Root foreverGraph (callerFrame ⟨0⟩) foreverTarget foreverFn := ⟨rfl, rfl, rfl⟩
private def beforeRestart : Phase := .label [] (.running [] foreverCode)
private def afterEntry : Phase := .label [] (.loop [] scalarBlock foreverBody (.running [] foreverBody) [])

private theorem foreverReady : Admitted foreverGraph foreverFn beforeRestart := .running rfl rfl

private theorem foreverEdge {out : Phase} :
    foreverGraph.Edge foreverChecked ⟨0⟩ beforeRestart out ↔ out = afterEntry := by
  rw [foreverGraph.edge_iff foreverChecked (fn := foreverFn) rfl]
  constructor
  · intro edge
    generalize eq : beforeRestart = src at edge
    cases edge <;> simp [beforeRestart, foreverCode, List.append_eq_nil_iff] at eq
    case loopEnter =>
      obtain ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩ := eq
      rfl
  · rintro rfl
    exact .loopEnter [] [] scalarBlock foreverBody []

private theorem foreverRestart {out : Phase} :
    foreverGraph.Edge foreverChecked ⟨0⟩ afterEntry out ↔ out = beforeRestart := by
  rw [foreverGraph.edge_iff foreverChecked (fn := foreverFn) rfl]
  constructor
  · intro edge
    cases edge with
    | loopStep _ _ _ _ inner =>
      generalize eq : Phase.label [] (.running [] foreverBody) = src at inner
      cases inner <;> simp [foreverBody, List.append_eq_nil_iff] at eq
      case branchHere =>
        obtain ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl⟩ := eq
        rfl
      case branchOuter =>
        obtain ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩ := eq
        exact (Nat.lt_irrefl 0 ‹_›).elim
  · rintro rfl
    exact .loopStep [] scalarBlock foreverBody [] (.branchHere [] [] [] [] [] rfl)

private theorem foreverEndpoints {out : Phase} :
    foreverGraph.Runs foreverChecked ⟨0⟩ beforeRestart out ↔ out = beforeRestart ∨ out = afterEntry := by
  constructor
  · intro run
    induction run with
    | refl => exact .inl rfl
    | tail _ edge ih =>
      rcases ih with rfl | rfl
      · exact .inr (foreverEdge.mp edge)
      · exact .inl (foreverRestart.mp edge)
  · rintro (rfl | rfl)
    · exact .refl
    · exact .single (foreverEdge.mpr rfl)

private theorem exactCycle {C : Type} {step : C → C → Prop} {dst : C}
    (render : Phase → C)
    (agree : Relation.ReflTransGen step (render beforeRestart) dst ↔
      ∃ out, foreverGraph.Runs foreverChecked ⟨0⟩ beforeRestart out ∧ Admitted foreverGraph foreverFn out ∧
        dst = render out) :
    Relation.ReflTransGen step (render beforeRestart) dst ↔
      dst = render beforeRestart ∨ dst = render afterEntry := by
  rw [agree]
  constructor
  · rintro ⟨out, run, _, rfl⟩
    rcases foreverEndpoints.mp run with rfl | rfl
    · exact .inl rfl
    · exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, .refl, foreverReady, rfl⟩
    · have edge := foreverEdge.mpr rfl
      exact ⟨_, .single edge, foreverGraph.admitted_step foreverChecked rfl foreverReady edge, rfl⟩

example {dst : Execution.Core.Config Unit} :=
  exactCycle (dst := dst) (coreConfig (coreStore foreverGraph) (callerFrame ⟨0⟩) foreverTarget)
    (core_run_iff (P := Numerics.Profile.spec) foreverChecked (coreAllocated _) foreverRoot foreverReady)

example {dst : Lime1.Execution.Config Unit} :=
  exactCycle (dst := dst) (limeConfig (limeStore foreverGraph) (callerFrame ⟨0⟩) foreverTarget)
    (lime_run_iff foreverChecked (limeAllocated _) foreverRoot foreverReady)

example {dst : V1.Execution.Config Unit} :=
  exactCycle (dst := dst) (v1Config (v1Store foreverGraph) (callerFrame ⟨0⟩) foreverTarget)
    (v1_run_iff foreverV1Checked (v1Allocated _) foreverRoot foreverReady rfl)

end ScalarLoops

section IndexedBlocks

private abbrev wide := NumType.int .i64
private abbrev wideVal := Value.int .i64
private abbrev narrowLocal : LocalIdx := ⟨2⟩
private abbrev wideLocal : LocalIdx := ⟨3⟩
private abbrev indexedType : TypeIdx := ⟨1⟩
private def mixedSig : V1.FuncType := ⟨[wide, int32], [int32, wide]⟩
private def mixedArgs : List Value := [wideVal 11, i32 7]
private def beforeMixed : List Value := mixedArgs ++ [i32 0, wideVal 0]
private def afterMixed : List Value := mixedArgs ++ [i32 7, wideVal 11]
private def mixedResults : List Value := [i32 7, wideVal 11]
private def flatBody : List Op := [.set narrowLocal, .set wideLocal, readLocal narrowLocal, readLocal wideLocal]
private def mixedCode : List Op := [.indexedBlock indexedType mixedSig flatBody]

private def mixedCallee : Function :=
  ⟨⟨{ types := [⟨[], []⟩, mixedSig] }, ⟨0⟩, mixedSig.params, [int32, wide], mixedSig.results⟩,
    0, mixedArgs, mixedCode⟩

private def mixedTarget : CallTarget := ⟨⟨0⟩, ⟨0⟩, mixedCallee.declaration⟩
private def mixedTail : List Op := [.set ⟨0⟩, add, readLocal ⟨0⟩]
private def mixedCaller : Function :=
  ⟨⟨{ funcs := [⟨0⟩] }, ⟨0⟩, [], [wide], [int32, wide]⟩, 1, [i32 9] ++ mixedArgs,
    .call mixedTarget :: mixedTail⟩
private def mixedGraph : Program := ⟨[some mixedCallee, some mixedCaller]⟩
private def mixedRootTarget : CallTarget := ⟨⟨0⟩, ⟨1⟩, mixedCaller.declaration⟩
private theorem mixedChecked : mixedGraph.check = true := rfl
private theorem mixedRoot : Root mixedGraph (callerFrame ⟨1⟩) mixedRootTarget mixedCaller := ⟨rfl, rfl, rfl⟩

example : ({ mixedCallee with code := [.indexedBlock ⟨2⟩ mixedSig flatBody] }).check = false := rfl
example : ({ mixedCallee with code := [.indexedBlock ⟨0⟩ mixedSig flatBody] }).check = false := rfl
example : ({ mixedCallee with code := [.indexedBlock indexedType ⟨[wide, int32], [wide, int32]⟩ flatBody] }).check = false := rfl
example : ({ mixedCallee with initial := [i32 7, wideVal 11] }).check = false := rfl
example : ({ mixedCallee with initial := [i32 7] }).check = false := rfl
example : ({ mixedCallee with code := [.indexedBlock indexedType mixedSig []] }).check = false := rfl
example : ({ mixedCallee with code := [.indexedBlock indexedType mixedSig [.br ⟨0⟩ [wide, int32]]] }).check = false := rfl

-- An unexecuted suffix and an unselected arm must still fit V1 source syntax.
private def skippedIndexed (code : List Op) (initial : List Value := []) : Program :=
  ⟨[some ⟨⟨{ types := [⟨[], []⟩] }, ⟨0⟩, [], [], []⟩, 0, initial, code⟩]⟩

private def skippedBlock : Op := .indexedBlock ⟨0⟩ ⟨[], []⟩ []

example : (skippedIndexed [.unreachable, skippedBlock]).check = true := rfl
example : (skippedIndexed [.unreachable, skippedBlock]).checkV1 = false := rfl
example : (skippedIndexed [.block none [.return_, skippedBlock]]).checkV1 = false := rfl
example : (skippedIndexed [.unreachable, .if_ none [] [skippedBlock]]).checkV1 = false := rfl

private theorem mixedLeafFinish {program : Program} {fn : Function} (checked : program.check = true)
    (found : program.lookup ⟨0⟩ = some fn) (tail : List Op)
    (leave : Layer fn (fun t => program.Edge checked t.address)
      (.label afterMixed (.running mixedResults tail)) (.exit afterMixed (.values mixedResults)) (.indexed mixedSig))
    (typed : fn.ResultTyped (.values mixedResults)) :
    program.Runs checked ⟨0⟩ (.label beforeMixed (.indexedBlock [] mixedSig (.running mixedArgs (flatBody ++ tail)) []))
      (.done (.values mixedResults)) := by
  have rule {a b : Phase} := (program.edge_iff checked (a := a) (b := b) found).mpr
  have setNarrow := Relation.ReflTransGen.single (rule (.indexedBlockStep [] mixedSig []
    (.localSet (saved := [wideVal 11]) (rest := [.set wideLocal, readLocal narrowLocal, readLocal wideLocal] ++ tail)
      (Locals.fact (.set beforeMixed narrowLocal (i32 7) (by decide))))))
  have setWide := setNarrow.tail (rule (.indexedBlockStep [] mixedSig []
    (.localSet (saved := []) (rest := [readLocal narrowLocal, readLocal wideLocal] ++ tail)
      (Locals.fact (.set (mixedArgs ++ [i32 7, wideVal 0]) wideLocal (wideVal 11) (by decide))))))
  have first := setWide.tail (rule (.indexedBlockStep [] mixedSig []
    (.numeric (locals := afterMixed) (rest := readLocal wideLocal :: tail)
      (.get (stack := []) (i := narrowLocal) (v := i32 7) rfl))))
  have second := first.tail (rule (.indexedBlockStep [] mixedSig []
    (.numeric (locals := afterMixed) (rest := tail) (.get (stack := [i32 7]) (i := wideLocal)
      (v := wideVal 11) rfl))))
  have completed := second.tail (rule (.indexedBlockStep [] mixedSig [] leave))
  exact (completed.tail (rule (.leaveValues afterMixed mixedResults))).tail
    (rule (.leaveFrame afterMixed (.values mixedResults) typed))

private theorem mixedLeafRun : mixedGraph.Runs mixedChecked ⟨0⟩ (.invoke mixedArgs) (.done (.values mixedResults)) := by
  have found : mixedGraph.lookup ⟨0⟩ = some mixedCallee := rfl
  have rule {a b : Phase} := (mixedGraph.edge_iff mixedChecked (a := a) (b := b) found).mpr
  have entered := (Relation.ReflTransGen.single (rule (.enter mixedArgs rfl))).tail
    (rule (.indexedBlockEnter beforeMixed [] mixedArgs indexedType mixedSig flatBody [] rfl rfl))
  exact entered.trans (mixedLeafFinish mixedChecked found [] (.leaveValues afterMixed mixedResults) rfl)

private abbrev mixedResumed : Phase := .label [wideVal 0] (.running ([i32 9] ++ mixedResults) mixedTail)

private theorem mixedResume {program : Program} (checked : program.check = true)
    (found : program.lookup ⟨1⟩ = some mixedCaller)
    (child : program.Runs checked ⟨0⟩ (.invoke mixedArgs) (.done (.values mixedResults))) :
    program.Runs checked ⟨1⟩ (.call []) mixedResumed := by
  have rule {a b : Phase} := (program.edge_iff checked (a := a) (b := b) found).mpr
  have start := (Relation.ReflTransGen.single (rule (.resolve []))).tail (rule (.enter [] rfl))
  exact start.trans (Program.compose_call checked (target := mixedTarget)
    (locals := [wideVal 0]) (saved := [i32 9]) (rest := mixedTail) found
    (by simp [mixedCaller, Function.targets, codeTargets, Op.targets, mixedTail, readLocal, add]) rfl child)

private theorem mixedFinish {program : Program} (checked : program.check = true)
    (found : program.lookup ⟨1⟩ = some mixedCaller) (resume : program.Runs checked ⟨1⟩ (.call []) mixedResumed) :
    program.Runs checked ⟨1⟩ (.call []) (.done (.values [i32 16, wideVal 11])) := by
  have rule {a b : Phase} := (program.edge_iff checked (a := a) (b := b) found).mpr
  have set := resume.tail (rule (.localSet (saved := [i32 9, i32 7]) (rest := [add, readLocal ⟨0⟩])
    (Locals.fact (.set [wideVal 0] ⟨0⟩ (wideVal 11) (by decide)))))
  have added := set.tail (rule (.numeric (rest := [readLocal ⟨0⟩]) (.bin (stack := [])
    (show Numerics.intBinOp .i32 .add 9 7 = .ok 16 from rfl))))
  have last := added.tail (rule (.numeric (locals := [wideVal 11]) (rest := [])
    (.get (stack := [i32 16]) (i := ⟨0⟩) (v := wideVal 11) rfl)))
  exact (last.tail (rule (.leaveValues [wideVal 11] [i32 16, wideVal 11]))).tail
    (rule (.leaveFrame [wideVal 11] (.values [i32 16, wideVal 11]) rfl))

private theorem checkedIndexedRun {program : Program} {caller : Execution.Runtime.Frame}
    {target : CallTarget} {fn : Function} {start out : Phase} (checked : program.check = true)
    (root : Root program caller target fn) (ready : Admitted program fn start)
    (run : program.Runs checked target.address start out) :
    Execution.Core.Steps Numerics.Profile.spec SingleThreaded.Det.noHost
      (coreConfig (coreStore program) caller target start) (coreConfig (coreStore program) caller target out) ∧
    Lime1.Execution.Steps CallFrame.limeNoHost
      (limeConfig (limeStore program) caller target start) (limeConfig (limeStore program) caller target out) := by
  have endpoint := Program.admitted_run checked root.found ready run
  exact ⟨(core_run_iff checked (coreAllocated _) root ready).mpr ⟨_, run, endpoint, rfl⟩,
    (lime_run_iff checked (limeAllocated _) root ready).mpr ⟨_, run, endpoint, rfl⟩⟩

private theorem checkedIndexedStep {program : Program} {caller : Execution.Runtime.Frame}
    {target : CallTarget} {fn : Function} {start out : Phase} (checked : program.check = true)
    (root : Root program caller target fn) (ready : Admitted program fn start)
    (edge : program.Edge checked target.address start out) :
    Execution.Core.Step Numerics.Profile.spec SingleThreaded.Det.noHost
      (coreConfig (coreStore program) caller target start) (coreConfig (coreStore program) caller target out) ∧
    Lime1.Execution.Step CallFrame.limeNoHost
      (limeConfig (limeStore program) caller target start) (limeConfig (limeStore program) caller target out) :=
  ⟨(core_step_iff checked (coreAllocated _) root ready).mpr ⟨_, edge, rfl⟩,
    (lime_step_iff checked (limeAllocated _) root ready).mpr ⟨_, edge, rfl⟩⟩

example := checkedIndexedRun mixedChecked mixedRoot (.call (args := []) rfl) (mixedResume mixedChecked rfl mixedLeafRun)
example := checkedIndexedRun mixedChecked mixedRoot (.call (args := []) rfl)
  (mixedFinish mixedChecked rfl (mixedResume mixedChecked rfl mixedLeafRun))

private def mixedBranch : List Op := [.br ⟨0⟩ mixedSig.results]
private def mixedIf : Op := .indexedIf indexedType mixedSig flatBody (flatBody ++ mixedBranch)
private def mixedIfCallee (condition : BitVec 32) : Function :=
  { mixedCallee with initial := mixedArgs ++ [i32 condition], code := [mixedIf] }
private def mixedIfGraph (condition : BitVec 32) : Program := ⟨[some (mixedIfCallee condition), some mixedCaller]⟩
private theorem mixedIfChecked (condition : BitVec 32) : (mixedIfGraph condition).check = true := rfl
private theorem mixedIfRoot (condition : BitVec 32) :
    Root (mixedIfGraph condition) (callerFrame ⟨1⟩) mixedRootTarget mixedCaller := ⟨rfl, rfl, rfl⟩

-- Both arms are checked, even when the initial condition is a known constant.
example : ({ mixedIfCallee 1 with code := [.indexedIf indexedType mixedSig flatBody []] }).check = false := rfl
example : ({ mixedIfCallee 0 with code := [.indexedIf indexedType mixedSig [] flatBody] }).check = false := rfl
example : ({ mixedIfCallee 1 with code := [.indexedIf ⟨0⟩ mixedSig flatBody flatBody] }).check = false := rfl
example : ({ mixedIfCallee 1 with code := [.indexedIf ⟨2⟩ mixedSig flatBody flatBody] }).check = false := rfl
example : ({ mixedIfCallee 1 with initial := [i32 7, wideVal 11, i32 1] }).check = false := rfl
example : ({ mixedIfCallee 1 with initial := [i32 1] ++ mixedArgs }).check = false := rfl
example : ({ mixedIfCallee 1 with initial := mixedArgs ++ [wideVal 1] }).check = false := rfl

private def scalarIndexedIf : Op := .indexedIf ⟨0⟩ ⟨[], []⟩ [] []
example : (skippedIndexed [scalarIndexedIf] [i32 0]).check = true := rfl
example : (skippedIndexed [scalarIndexedIf] [i32 0]).checkV1 = false := rfl
example : (skippedIndexed [.unreachable, scalarIndexedIf]).checkV1 = false := rfl
example : (skippedIndexed [.if_ none [] [.unreachable, scalarIndexedIf]] [i32 1]).check = true := rfl
example : (skippedIndexed [.if_ none [] [.unreachable, scalarIndexedIf]] [i32 1]).checkV1 = false := rfl

private abbrev mixedIfSource (condition : BitVec 32) : Phase :=
  .label beforeMixed (.running (mixedArgs ++ [i32 condition]) [mixedIf])

private abbrev mixedIfSelected (condition : BitVec 32) : Phase :=
  .label beforeMixed (.running mixedArgs
    [.indexedBlock indexedType mixedSig (if condition = 0 then flatBody ++ mixedBranch else flatBody)])

private theorem mixedIfSelect (condition : BitVec 32) :
    (mixedIfGraph condition).Edge (mixedIfChecked condition) ⟨0⟩ (mixedIfSource condition) (mixedIfSelected condition) :=
  ((mixedIfGraph condition).edge_iff (mixedIfChecked condition) (fn := mixedIfCallee condition) rfl).mpr
    (.indexedIfSelect beforeMixed mixedArgs condition indexedType mixedSig flatBody (flatBody ++ mixedBranch) [])

example (condition : BitVec 32) :=
  have root : Root (mixedIfGraph condition) (callerFrame ⟨0⟩) mixedTarget (mixedIfCallee condition) := ⟨rfl, rfl, rfl⟩
  have ready : Admitted (mixedIfGraph condition) (mixedIfCallee condition) (mixedIfSource condition) := .running rfl rfl
  checkedIndexedStep (mixedIfChecked condition) root ready (mixedIfSelect condition)

private theorem mixedIfLeafRun (condition : BitVec 32) :
    (mixedIfGraph condition).Runs (mixedIfChecked condition) ⟨0⟩ (.invoke mixedArgs) (.done (.values mixedResults)) := by
  have found : (mixedIfGraph condition).lookup ⟨0⟩ = some (mixedIfCallee condition) := rfl
  have rule {a b : Phase} := ((mixedIfGraph condition).edge_iff (mixedIfChecked condition) (a := a) (b := b) found).mpr
  have selected := (Relation.ReflTransGen.single (rule (.enter mixedArgs rfl))).tail (mixedIfSelect condition)
  by_cases zero : condition = 0
  · simp only [mixedIfSelected, ite_eq_left zero] at selected
    have entered := selected.tail (rule (.indexedBlockEnter beforeMixed [] mixedArgs indexedType mixedSig
      (flatBody ++ mixedBranch) [] rfl rfl))
    exact entered.trans (mixedLeafFinish (mixedIfChecked condition) found mixedBranch
      (.branchHere (kind := .indexed mixedSig) afterMixed [] mixedResults mixedSig.results [] rfl) rfl)
  · simp only [mixedIfSelected, ite_eq_right zero] at selected
    have entered := selected.tail (rule (.indexedBlockEnter beforeMixed [] mixedArgs indexedType mixedSig flatBody [] rfl rfl))
    exact entered.trans (mixedLeafFinish (mixedIfChecked condition) found [] (.leaveValues afterMixed mixedResults) rfl)

-- Both arms return [i32 7, i64 11]. The caller resumes with its i32 9
-- prefix and original locals, then consumes the two delivered operands.
private theorem mixedIfResume (condition : BitVec 32) :
    (mixedIfGraph condition).Runs (mixedIfChecked condition) ⟨1⟩ (.call []) mixedResumed :=
  mixedResume (mixedIfChecked condition) rfl (mixedIfLeafRun condition)

example := checkedIndexedRun (mixedIfChecked 1) (mixedIfRoot 1) (.call (args := []) rfl) (mixedIfResume 1)
example := checkedIndexedRun (mixedIfChecked 0) (mixedIfRoot 0) (.call (args := []) rfl) (mixedIfResume 0)
example (condition : BitVec 32) := checkedIndexedRun (mixedIfChecked condition) (mixedIfRoot condition)
  (.call (args := []) rfl) (mixedFinish (mixedIfChecked condition) rfl (mixedIfResume condition))

private def loopSig : V1.FuncType := ⟨[wide, int32], [wide]⟩
private def loopSaved : List Value := [i32 9]
private def loopArgs : List Value := [i32 1]
private def loopLocals (flag : BitVec 32) : List Value := [i32 flag, i32 0, i32 0]
private def loopRemainder : List Op := [.set ⟨2⟩]
private def loopTest : Op := .brIf ⟨0⟩ loopSig.params
private def indexedLoopBody : List Op := [readLocal ⟨0⟩, readLocal ⟨1⟩, .set ⟨0⟩, loopTest] ++ loopRemainder
private def indexedLoopCode : List Op := [.indexedLoop indexedType loopSig indexedLoopBody]
private def indexedLoopFn : Function :=
  ⟨⟨{ types := [⟨[int32], [int32, wide]⟩, loopSig] }, ⟨0⟩, [int32], [int32, int32], [int32, wide]⟩,
    0, loopSaved ++ mixedArgs, indexedLoopCode⟩
private def indexedLoopGraph : Program := ⟨[some indexedLoopFn]⟩
private def indexedLoopTarget : CallTarget := ⟨⟨0⟩, ⟨0⟩, indexedLoopFn.declaration⟩
private theorem indexedLoopChecked : indexedLoopGraph.check = true := rfl
private theorem indexedLoopRoot : Root indexedLoopGraph (callerFrame ⟨0⟩) indexedLoopTarget indexedLoopFn := ⟨rfl, rfl, rfl⟩

example : ({ indexedLoopFn with code := [.indexedLoop ⟨2⟩ loopSig indexedLoopBody] }).check = false := rfl
example : ({ indexedLoopFn with code := [.indexedLoop indexedType mixedSig indexedLoopBody] }).check = false := rfl
example : ({ indexedLoopFn with initial := loopSaved ++ mixedArgs.reverse }).check = false := rfl
example : ({ indexedLoopFn with code := [.indexedLoop indexedType loopSig []] }).check = false := rfl
example : ({ indexedLoopFn with code := [.indexedLoop indexedType loopSig [.br ⟨0⟩ loopSig.results]] }).check = false := rfl
example : ({ indexedLoopFn with code := [.indexedLoop indexedType loopSig [.set ⟨2⟩, .br ⟨0⟩ loopSig.params]] }).check = false := rfl

private def emptyIndexedLoop : Op := .indexedLoop ⟨0⟩ ⟨[], []⟩ []
example : (skippedIndexed [emptyIndexedLoop]).check = true := rfl
example : (skippedIndexed [emptyIndexedLoop]).checkV1 = false := rfl
example : (skippedIndexed [.unreachable, emptyIndexedLoop]).check = true := rfl
example : (skippedIndexed [.unreachable, emptyIndexedLoop]).checkV1 = false := rfl

private abbrev indexedLoopPending (flag : BitVec 32) : Phase :=
  .label (loopLocals flag) (.running (loopSaved ++ mixedArgs) indexedLoopCode)

private abbrev indexedIteration (locals stack : List Value) (code : List Op) : Phase :=
  .label locals (.indexedLoop loopSaved indexedType loopSig indexedLoopBody (.running stack code) [])

private theorem indexedLoopEdge {a b : Phase}
    (step : Layer indexedLoopFn (fun t => indexedLoopGraph.Edge indexedLoopChecked t.address) a b) :
    indexedLoopGraph.Edge indexedLoopChecked ⟨0⟩ a b :=
  (indexedLoopGraph.edge_iff indexedLoopChecked (fn := indexedLoopFn) rfl).mpr step

private theorem mixedReentry (flag : BitVec 32) :
    indexedLoopGraph.Edge indexedLoopChecked ⟨0⟩ (indexedLoopPending flag)
      (indexedIteration (loopLocals flag) mixedArgs indexedLoopBody) :=
  indexedLoopEdge (.indexedLoopEnter (loopLocals flag) loopSaved mixedArgs indexedType loopSig indexedLoopBody [] rfl rfl)

private theorem mixedIterationTest (flag : BitVec 32) :
    indexedLoopGraph.Runs indexedLoopChecked ⟨0⟩ (indexedLoopPending flag)
      (indexedIteration (loopLocals 0) (mixedArgs ++ [i32 flag]) (loopTest :: loopRemainder)) := by
  have step {locals : List Value} {body : Body} {next : Phase}
      (edge : Layer indexedLoopFn (fun t => indexedLoopGraph.Edge indexedLoopChecked t.address)
        (.label locals body) next (.indexedLoop indexedType loopSig indexedLoopBody)) :=
    indexedLoopEdge (.indexedLoopStep loopSaved indexedType loopSig indexedLoopBody [] edge)
  have savedFlag := (Relation.ReflTransGen.single (mixedReentry flag)).tail (step
    (.numeric (locals := loopLocals flag) (rest := [readLocal ⟨1⟩, .set ⟨0⟩, loopTest] ++ loopRemainder)
      (.get (stack := mixedArgs) (i := ⟨0⟩) (v := i32 flag) rfl)))
  have zero := savedFlag.tail (step
    (.numeric (locals := loopLocals flag) (rest := [.set ⟨0⟩, loopTest] ++ loopRemainder)
      (.get (stack := mixedArgs ++ [i32 flag]) (i := ⟨1⟩) (v := i32 0) rfl)))
  exact zero.tail (step (.localSet (saved := mixedArgs ++ [i32 flag]) (rest := loopTest :: loopRemainder)
    (Locals.fact (.set (loopLocals flag) ⟨0⟩ (i32 0) (by change 0 < 3; decide)))))

private abbrev mixedBranchSource : Phase :=
  indexedIteration (loopLocals 0) mixedArgs (.br ⟨0⟩ loopSig.params :: loopRemainder)

private theorem firstMixedIteration :
    indexedLoopGraph.Runs indexedLoopChecked ⟨0⟩ (.call loopArgs) mixedBranchSource := by
  have entered := (Relation.ReflTransGen.single (indexedLoopEdge (.resolve loopArgs))).tail
    (indexedLoopEdge (.enter loopArgs rfl))
  exact (entered.trans (mixedIterationTest 1)).tail (indexedLoopEdge
    (.indexedLoopStep loopSaved indexedType loopSig indexedLoopBody []
      (.branchIf (loopLocals 0) mixedArgs 1 ⟨0⟩ loopSig.params loopRemainder)))

private theorem mixedBackEdge :
    indexedLoopGraph.Edge indexedLoopChecked ⟨0⟩ mixedBranchSource (indexedLoopPending 0) :=
  indexedLoopEdge (.indexedLoopStep loopSaved indexedType loopSig indexedLoopBody []
    (.branchHere (kind := .indexedLoop indexedType loopSig indexedLoopBody)
      (loopLocals 0) [] mixedArgs loopSig.params loopRemainder rfl))

-- The back edge reinstates the pending instruction with its two ordered operands.
-- The second step consumes that suffix into the new label without resetting the flag.
example :=
  have ready := Program.admitted_run indexedLoopChecked indexedLoopRoot.found (.call (args := loopArgs) rfl) firstMixedIteration
  checkedIndexedStep indexedLoopChecked indexedLoopRoot ready mixedBackEdge

example :=
  have ready := Program.admitted_run indexedLoopChecked indexedLoopRoot.found (.call (args := loopArgs) rfl)
    (firstMixedIteration.tail mixedBackEdge)
  checkedIndexedStep indexedLoopChecked indexedLoopRoot ready (mixedReentry 0)

private theorem indexedLoopReturns : indexedLoopGraph.Runs indexedLoopChecked ⟨0⟩ (.call loopArgs)
    (.done (.values [i32 9, wideVal 11])) := by
  have ready := (firstMixedIteration.tail mixedBackEdge).trans (mixedIterationTest 0)
  have notTaken := ready.tail (indexedLoopEdge (.indexedLoopStep loopSaved indexedType loopSig indexedLoopBody []
    (.branchIf (loopLocals 0) mixedArgs 0 ⟨0⟩ loopSig.params loopRemainder)))
  have consume := notTaken.tail (indexedLoopEdge (.indexedLoopStep loopSaved indexedType loopSig indexedLoopBody []
    (.localSet (saved := [wideVal 11]) (rest := [])
      (Locals.fact (.set (loopLocals 0) ⟨2⟩ (i32 7) (by decide))))))
  let locals : List Value := [i32 0, i32 0, i32 7]
  have leave := consume.tail (indexedLoopEdge (.indexedLoopStep loopSaved indexedType loopSig indexedLoopBody []
    (.leaveValues locals [wideVal 11])))
  exact (leave.tail (indexedLoopEdge (.leaveValues locals [i32 9, wideVal 11]))).tail
    (indexedLoopEdge (.leaveFrame locals (.values [i32 9, wideVal 11]) rfl))

example := checkedIndexedRun indexedLoopChecked indexedLoopRoot (.call (args := loopArgs) rfl) indexedLoopReturns

-- An explicit return delivers the i32 function result while dropping the i64
-- operand and the pending code in both the loop and the surrounding function label.
private def returnLoopBody : List Op := [.return_, .unreachable]
private def returnLoopTail : List Op := [.set ⟨1⟩, readLocal ⟨0⟩]
private def returnLoopFn : Function :=
  ⟨⟨{ types := [⟨[], [int32]⟩, loopSig] }, ⟨0⟩, [], [int32, wide], [int32]⟩, 0, mixedArgs,
    .indexedLoop indexedType loopSig returnLoopBody :: returnLoopTail⟩
private def returnLoopGraph : Program := ⟨[some returnLoopFn]⟩
private def returnLoopTarget : CallTarget := ⟨⟨0⟩, ⟨0⟩, returnLoopFn.declaration⟩
private theorem returnLoopChecked : returnLoopGraph.check = true := rfl
private theorem returnLoopRoot : Root returnLoopGraph (callerFrame ⟨0⟩) returnLoopTarget returnLoopFn := ⟨rfl, rfl, rfl⟩

private theorem returnThroughIndexedLoop : returnLoopGraph.Runs returnLoopChecked ⟨0⟩ (.call []) (.done (.values [i32 7])) := by
  have rule {a b : Phase} := (returnLoopGraph.edge_iff returnLoopChecked (a := a) (b := b) returnLoopRoot.found).mpr
  let locals : List Value := [i32 0, wideVal 0]
  have activation := (Relation.ReflTransGen.single (rule (.resolve []))).tail (rule (.enter [] rfl))
  have entered := activation.tail (rule (.indexedLoopEnter locals [] mixedArgs indexedType loopSig returnLoopBody returnLoopTail rfl rfl))
  have acrossLoop := entered.tail (rule (.indexedLoopStep [] indexedType loopSig returnLoopBody returnLoopTail
    (.returnLabel locals mixedArgs [.unreachable])))
  exact (acrossLoop.tail (rule (.returnLabel locals mixedArgs returnLoopTail))).tail
    (rule (.returnFrame locals [wideVal 11] [i32 7] rfl))

example := checkedIndexedRun returnLoopChecked returnLoopRoot (.call (args := []) rfl) returnThroughIndexedLoop

end IndexedBlocks

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
