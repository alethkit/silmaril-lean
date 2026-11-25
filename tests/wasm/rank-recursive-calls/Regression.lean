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
  exact (v1_step_iff (writingV1Checked false) (v1Allocated _) (writingRoot false) ready).mpr
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
  (v1_run_iff (writingV1Checked traps) (v1Allocated _) (writingRoot traps) (.call rfl)).mpr
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
  (v1_run_iff (blockV1Checked early traps) (v1Allocated _) (blockRoot early traps) (.call rfl)).mpr
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
    (v1_run_iff (ifV1Checked takeThen early traps) (v1Allocated _) root ready).mpr ⟨_, run, endpoint, rfl⟩⟩

example := ifNative ifThenRun
example := ifNative ifElseRun
example := ifNative ifReturnRun
example := ifNative ifTrapRun

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
