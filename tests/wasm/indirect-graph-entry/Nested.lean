import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control.Thms
import Silmaril.Wasm.Institution.Operational.Locals.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame FuncAddr Value)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private abbrev spec := Numerics.Profile.spec

private def signature : V1.FuncType := ⟨[.int .i64, .int .i32], [.int .i32, .int .i64]⟩
private def ownerType : V1.FuncType :=
  ⟨[.int .i32, .int .i32, .int .i64, .int .i32], [.int .i64, .int .i64, .int .i32, .int .i64]⟩

private def callee : Graph.Function :=
  ⟨⟨{ types := [signature] }, ⟨0⟩, signature.params, [], signature.results⟩, 0, [],
    [.numeric (.get ⟨1⟩), .numeric (.get ⟨0⟩)]⟩

private def owner : Graph.Function :=
  ⟨⟨{ types := [ownerType, signature], tables := [⟨0⟩] }, ⟨0⟩, ownerType.params, [.int .i64], ownerType.results⟩,
    0, [i64 7], [.unreachable]⟩

private def program : Graph.Program := ⟨[some callee, some owner]⟩
private def refs : List (Option FuncAddr) := [some ⟨0⟩, none]
private def tables : Source.Tables := [⟨refs, some 1⟩]
private def outer : Frame := ⟨[i32 77], { funcs := [⟨1⟩] }⟩
private def args (divisor selector : BitVec 32) : List Value := [i32 divisor, i32 selector, i64 42, i32 455]
private def divide : Prefix.Op := .bin .i32 (.div .unsigned)
private def selector : Prefix.Op := .get ⟨1⟩

private def outerBlock : Context.Resume.Block :=
  ⟨some (.int .i64), [.numeric (.get ⟨0⟩), .numeric (.get ⟨4⟩)]⟩
private def middleBlock : Context.Resume.Block :=
  ⟨some (.int .i32), [.set ⟨0⟩, .numeric (.get ⟨4⟩)]⟩
private def innerBlock : Context.Resume.Block :=
  ⟨some (.int .i32), [.numeric (.get ⟨0⟩), .numeric (.bin .i32 .add)]⟩

private def cont : Context.Resume.Continuation :=
  ⟨⟨1⟩, owner, [.set ⟨4⟩], [outerBlock, middleBlock, innerBlock]⟩

private def entry : GraphEntry.Entry :=
  ⟨cont, ⟨⟨1⟩, signature⟩, [.get ⟨2⟩, .get ⟨3⟩, .get ⟨0⟩, divide, selector]⟩

private def states (divisor : BitVec 32) : List OperandState :=
  [([], entry.before), ([i64 42], [.get ⟨3⟩, .get ⟨0⟩, divide, selector]),
    ([i64 42, i32 455], [.get ⟨0⟩, divide, selector]), ([i64 42, i32 455, i32 divisor], [divide, selector])]

private def normal : List OperandState := states 91 ++ [([i64 42, i32 5], [selector])]
private def atLookup (selected : BitVec 32) : List Value := [i64 42, i32 5, i32 selected]

private def active (selected : BitVec 32) : Source.Activation :=
  ⟨entry.frame (args 91 selected), ⟨⟨0⟩, ⟨⟨refs, some 1⟩, ⟨1⟩, signature⟩⟩, ⟨[], [i64 42, i32 5], selected⟩⟩

private theorem checked (divisor selected : BitVec 32) : entry.Checked program tables outer ⟨0⟩
    (args divisor selected) :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem ready (selected : BitVec 32) :
    entry.AtSite program tables outer ⟨0⟩ (args 91 selected) normal (atLookup selected) (active selected) :=
  ⟨checked .., .value (.get rfl) (.value (.get rfl) (.value (.get rfl)
    (.value (.bin (stack := [i64 42]) (x := 455) (y := 91) rfl) (.value (.get rfl) (.done _))))),
    rfl⟩

private theorem zeroTrace :
    entry.OperandTrace (args 0 0) (states 0) (.trap [i64 42] [selector]) :=
  .value (.get rfl) (.value (.get rfl) (.value (.get rfl)
    (.trap (.trap (stack := [i64 42]) (x := 455) (y := 0) (cause := .divideByZero) rfl))))

-- The block is entered on an empty stack. The saved i64 belongs to the function label.
example : entry.initial = [] := rfl
example : cont.scopes = [⟨1, [i64 7], outerBlock.tail⟩, ⟨1, [], middleBlock.tail⟩, ⟨1, [], innerBlock.tail⟩] := rfl
example : (active 1).resolve program = some .null := rfl
example : { entry with cont := { cont with blocks := [outerBlock, { middleBlock with result := some (.int .i64) }, innerBlock] } }.check
    program tables = false := rfl
example : { entry with cont := { cont with blocks := [outerBlock, { middleBlock with tail := [] }, innerBlock] } }.check
    program tables = false := rfl

private def coreStore : Core.Store Unit :=
  { funcs := [callee.coreInstance, entry.coreInstance], tables := tables.map Runtime.TableInst.toCore }
private def limeStore : Lime1.Execution.Store Unit :=
  { funcs := [.wasm callee.declaration.type callee.declaration.module callee.limeFunc, entry.limeInstance], tables }

private theorem noDirectTargets {address : FuncAddr} {fn : Graph.Function}
    (found : program.lookup address = some fn) : fn.targets = [] := by
  rcases address with ⟨_ | _ | n⟩
  · obtain rfl := Option.some.inj found.symm
    rfl
  · obtain rfl := Option.some.inj found.symm
    rfl
  · cases found

private theorem tableTarget {address : FuncAddr} (used : some address ∈ refs) : address = ⟨0⟩ := by
  simpa [refs] using used

private theorem coreAllocated (selected : BitVec 32) :
    entry.CoreAllocated program tables (active selected) coreStore := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro _ _ found target used
    rw [noDirectTargets found] at used
    cases used
  · intro _ _ found
    simp [coreStore, List.getElem?_map, found]
  · intro address fn used found
    obtain rfl := tableTarget used
    obtain rfl := Option.some.inj found.symm
    rfl

private theorem limeAllocated (selected : BitVec 32) :
    entry.LimeAllocated program tables (active selected) limeStore := by
  refine ⟨rfl, ?_, fun _ _ found => found, ?_⟩
  · intro _ _ found target used
    rw [noDirectTargets found] at used
    cases used
  · intro address fn used found
    obtain rfl := tableTarget used
    obtain rfl := Option.some.inj found.symm
    rfl

private def call : Context.Invocation :=
  ⟨(active 0).binding.site, entry.frame (args 91 0), 0, [], [i64 42, i32 5], ⟨0⟩, callee⟩
private theorem invoked : (active 0).invocation program = some call := rfl

example : (entry.corePrefix coreStore outer ⟨0⟩ (args 91 0) (active 0) (.resolved ⟨0⟩) normal).length = 14 := rfl
example : (entry.limePrefix limeStore outer ⟨0⟩ (args 91 0) (active 0) (.resolved ⟨0⟩) normal).length = 12 := rfl

-- The source block and its entered label are distinct prefix endpoints.
example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 91 0))
    (entry.coreOperands coreStore outer (args 91 0) ([], entry.before)) :=
  (core_run_iff (ready 0) (coreAllocated 0) invoked).mpr (.inl (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 91 0))
    (entry.limeOperands limeStore outer (args 91 0) ([], entry.before)) :=
  (lime_run_iff (ready 0) (limeAllocated 0) invoked).mpr (.inl (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))

private theorem calleeRun : program.FrameRuns ⟨0⟩ call.entered (.done (.values [i32 5, i64 42])) := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) (fn := callee) (address := ⟨0⟩) rfl).mpr
  have first := Relation.ReflTransGen.single (edge (.numeric (locals := [i64 42, i32 5])
    (rest := [.numeric (.get ⟨0⟩)]) (.get (stack := []) (i := ⟨1⟩) (v := i32 5) rfl)))
  have second := first.tail (edge (.numeric (rest := []) (.get (stack := [i32 5]) (i := ⟨0⟩) (v := i64 42) rfl)))
  exact (second.tail (edge (.leaveValues [i64 42, i32 5] [i32 5, i64 42]))).tail
    (edge (.leaveFrame _ (.values [i32 5, i64 42]) rfl))

private def stored : List Value := args 91 0 ++ [i64 42]
private def updated : List Value := args 96 0 ++ [i64 42]
private def results : List Value := [i64 7, i64 42, i32 96, i64 42]

private theorem resumed : Context.Resume.Runs program call cont (.callee call.entered)
    (.caller (.label updated (.running [i64 7, i64 42] outerBlock.tail))) := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) (fn := owner) (address := ⟨1⟩) rfl).mpr
  have before := Context.Resume.of_callee_run (cont := cont) (resume_guard (ready 0) invoked).1 calleeRun
  have writeResult := Locals.fact (.set (entry.frame (args 91 0)).locals ⟨4⟩ (i64 42) (by decide))
  have assign := before.tail (.resume (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail (.blockStep [] innerBlock.result innerBlock.tail
      (.localSet (saved := [i32 5]) (rest := []) writeResult))))))
  have innerExit := assign.tail (.caller (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail (.blockStep [] innerBlock.result innerBlock.tail
      (.leaveValues stored [i32 5]))))))
  have read := innerExit.tail (.caller (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail (.numeric (locals := stored)
      (rest := [.numeric (.bin .i32 .add)]) (.get (stack := [i32 5]) (i := ⟨0⟩) (v := i32 91) rfl))))))
  have add := read.tail (.caller (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail (.numeric (locals := stored) (rest := [])
      (.bin (stack := []) (x := 5) (y := 91) (z := 96) (op := .add) rfl))))))
  have middleExit := add.tail (.caller (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail (.leaveValues stored [i32 96])))))
  have writeSum := Locals.fact (.set stored ⟨0⟩ (i32 96) (by decide))
  have assignSum := middleExit.tail (.caller (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.localSet (saved := []) (rest := [.numeric (.get ⟨4⟩)]) writeSum))))
  have readResult := assignSum.tail (.caller (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.numeric (rest := []) (.get (stack := []) (i := ⟨4⟩) (v := i64 42) (locals := updated) rfl)))))
  exact readResult.tail (.caller (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.leaveValues updated [i64 42]))))

private theorem finished : Context.Resume.Runs program call cont (.callee call.entered)
    (.caller (.done (.values results))) := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) (fn := owner) (address := ⟨1⟩) rfl).mpr
  have first := resumed.tail (.caller (edge (.numeric (locals := updated) (rest := [.numeric (.get ⟨4⟩)])
    (.get (stack := [i64 7, i64 42]) (i := ⟨0⟩) (v := i32 96) rfl))))
  have last := first.tail (.caller (edge (.numeric (rest := [])
    (.get (stack := [i64 7, i64 42, i32 96]) (i := ⟨4⟩) (v := i64 42) rfl))))
  exact (last.tail (.caller (edge (.leaveValues updated results)))).tail
    (.caller (edge (.leaveFrame updated (.values results) rfl)))

-- The innermost tail saves the returned i64. The next tail computes 96
-- from the returned i32. The third tail saves 96 and delivers the i64.
-- The function tail reads both updated locals after all three label exits.
example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 91 0))
    ⟨coreStore, outer.toCore, coreValues results⟩ :=
  (core_run_iff (ready 0) (coreAllocated 0) invoked).mpr (.inr ⟨_, finished, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 91 0))
    ⟨limeStore, outer, Lime1.Execution.values results⟩ :=
  (lime_run_iff (ready 0) (limeAllocated 0) invoked).mpr (.inr ⟨_, finished, rfl⟩)

private theorem discardAll {A : Type} (stack : List Value) (rest : List A)
    (pending : stack ≠ [] ∨ rest ≠ []) : Prefix.Discard stack rest [] [] := by
  simpa only [List.nil_append, List.append_nil] using Prefix.Discard.cut [] stack rest [] pending

private def trapScopes {A : Type} (emit : Graph.Op → A) : List (Blocks.Context.Scope A) :=
  [⟨1, [], innerBlock.tail.map emit⟩, ⟨1, [], middleBlock.tail.map emit⟩, ⟨1, [i64 7], outerBlock.tail.map emit⟩]

private theorem twoExits {A : Type} (emit : Graph.Op → A) (x : Value) (xs : List Value) (rest : List A) :
    CleanupRuns (.label (x :: xs) rest (trapScopes emit))
      (.label [] (middleBlock.tail.map emit) [⟨1, [i64 7], outerBlock.tail.map emit⟩]) := by
  have first : CleanupRuns (.label (x :: xs) rest (trapScopes emit))
      (.label [] (innerBlock.tail.map emit) [⟨1, [], middleBlock.tail.map emit⟩, ⟨1, [i64 7], outerBlock.tail.map emit⟩]) :=
    (Relation.ReflTransGen.single (.discard (discardAll (x :: xs) rest (.inl (by simp))))).tail (.blockExit _ _)
  exact (first.tail (.discard (discardAll [] _ (.inr (by simp [innerBlock]))))).tail (.blockExit _ _)

private theorem unwind {A : Type} (emit : Graph.Op → A) (x : Value) (xs : List Value) (rest : List A) :
    CleanupRuns (.label (x :: xs) rest (trapScopes emit)) .done := by
  have outerTrap := ((twoExits emit x xs rest).tail (.discard (discardAll [] _ (.inr (by simp [middleBlock]))))).tail
    (.blockExit ⟨1, [i64 7], outerBlock.tail.map emit⟩ [])
  exact ((outerTrap.tail (.discard (discardAll [i64 7] _ (.inl (by simp))))).tail .label).tail .frame

-- A prefix trap uses only the native entry allocation. Two steps across
-- labels leave the last block's tail pending and the saved i64 outside it.
private def coreNoTable := { coreStore with tables := [] }

example : Core.Steps spec noHost (coreSource coreNoTable outer ⟨0⟩ (args 0 0))
    (entry.coreCleanup coreNoTable outer (entry.frame (args 0 0))
      (.label [] (middleBlock.tail.map Graph.coreEmit) [⟨1, [i64 7], outerBlock.tail.map Graph.coreEmit⟩])) :=
  (core_operand_trap_run_iff (checked 0 0) rfl zeroTrace).mpr
    (.inr ⟨_, twoExits Graph.coreEmit (i64 42) [] _, rfl⟩)

example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 91 1))
    ⟨coreStore, outer.toCore, [.trap]⟩ :=
  (core_trap_run_iff (ready 1) (coreAllocated 1) rfl .null).mpr
    (.inr ⟨.done, unwind Graph.coreEmit (i64 42) [i32 5] _, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 91 1))
    ⟨limeStore, outer, [.trap]⟩ :=
  (lime_trap_run_iff (ready 1) (limeAllocated 1) rfl .null).mpr
    (.inr ⟨.done, unwind Graph.limeEmit (i64 42) [i32 5] _, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 0 0))
    ⟨limeStore, outer, [.trap]⟩ :=
  (lime_operand_trap_run_iff (checked 0 0) rfl zeroTrace).mpr
    (.inr ⟨.done, unwind Graph.limeEmit (i64 42) [] _, rfl⟩)

namespace ConditionalFixture

private def conditional : Conditional.Entry :=
  { inside := { entry with cont := { cont with blocks := [middleBlock, innerBlock] } }
    condition := ⟨1⟩
    result := outerBlock.result
    alternate := [.numeric (.get ⟨2⟩)]
    tail := outerBlock.tail
    siteOnTrue := false }

private theorem conditionReady (divisor selected : BitVec 32) :
    conditional.Checked program tables outer ⟨0⟩ (args divisor selected) :=
  ⟨rfl, rfl, rfl, rfl⟩

example : conditional.site = entry := rfl
example : conditional.choosesSite 0 = true := rfl
example : conditional.choosesSite 1 = false := rfl

-- Both arms are checked against the same i64 result.
example : { conditional with alternate := [.numeric (.get ⟨0⟩)] }.check program tables = false := rfl
example : { conditional with inside := { conditional.inside with before := [.get ⟨99⟩] } }.check
    program tables = false := rfl
example : { conditional with condition := ⟨2⟩ }.check program tables = false := rfl

private def coreConditional (c : Conditional.Entry) (hasTable : Bool) : Core.Store Unit :=
  { coreStore with
    funcs := [callee.coreInstance, c.coreInstance]
    tables := if hasTable then coreStore.tables else [] }

private def limeConditional (c : Conditional.Entry) (hasTable : Bool) : Lime1.Execution.Store Unit :=
  { limeStore with
    funcs := [.wasm callee.declaration.type callee.declaration.module callee.limeFunc, c.limeInstance]
    tables := if hasTable then limeStore.tables else [] }

private theorem coreTables (c : Conditional.Entry) : Source.Tables.CoreAllocated tables (coreConditional c true) :=
  (coreAllocated 0).tables

private theorem limeTables (c : Conditional.Entry) : Source.Tables.LimeAllocated tables (limeConditional c true) :=
  (limeAllocated 0).tables

private theorem coreLinks (c : Conditional.Entry) (hasTable : Bool) :
    program.CoreLinksAllocated (coreConditional c hasTable) := by
  intro _ _ found target used
  rw [noDirectTargets found] at used
  cases used

private theorem limeLinks (c : Conditional.Entry) (hasTable : Bool) :
    program.LimeLinksAllocated (limeConditional c hasTable) := by
  intro _ _ found target used
  rw [noDirectTargets found] at used
  cases used

private theorem coreTargets (c : Conditional.Entry) (selected : BitVec 32) :
    (active selected).binding.site.CoreAllocated program (coreConditional c true) := by
  intro address fn used found
  obtain rfl := tableTarget used
  obtain rfl := Option.some.inj found.symm
  rfl

private theorem limeTargets (c : Conditional.Entry) (selected : BitVec 32) :
    (active selected).binding.site.LimeAllocated program (limeConditional c true) := by
  intro address fn used found
  obtain rfl := tableTarget used
  obtain rfl := Option.some.inj found.symm
  rfl

example : Core.Steps spec noHost (coreSource (coreConditional conditional true) outer ⟨0⟩ (args 91 0))
    ⟨coreConditional conditional true, outer.toCore, coreValues results⟩ :=
  (Conditional.core_site_run (conditionReady 91 0) rfl rfl rfl (ready 0)
    (coreTables conditional) (coreTargets conditional 0) (coreLinks conditional true) invoked).mpr
      (.inr ⟨_, finished, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeSource (limeConditional conditional true) outer ⟨0⟩ (args 91 0))
    ⟨limeConditional conditional true, outer, Lime1.Execution.values results⟩ :=
  (Conditional.lime_site_run (conditionReady 91 0) rfl rfl rfl (ready 0)
    (limeTables conditional) (limeTargets conditional 0) (limeLinks conditional true) invoked).mpr
      (.inr ⟨_, finished, rfl⟩)

private def alternateLocals : List Value := args 0 1 ++ [i64 0]
private def alternateResults : List Value := [i64 7, i64 42, i32 0, i64 0]

private theorem alternateFinished : program.FrameRuns ⟨1⟩ (conditional.alternatePhase (args 0 1))
    (.done (.values alternateResults)) := by
  have edge {a b : Graph.Phase} :=
    (program.frameEdge_iff (a := a) (b := b) (fn := owner) (address := ⟨1⟩) rfl).mpr
  have enter := Relation.ReflTransGen.single (edge (.blockEnter alternateLocals [i64 7] outerBlock.result
    conditional.alternate outerBlock.tail))
  have read := enter.tail (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.numeric (rest := []) (.get (stack := []) (i := ⟨2⟩) (v := i64 42) (locals := alternateLocals) rfl))))
  have leave := read.tail (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.leaveValues alternateLocals [i64 42])))
  have first := leave.tail (edge (.numeric (locals := alternateLocals) (rest := [.numeric (.get ⟨4⟩)])
    (.get (stack := [i64 7, i64 42]) (i := ⟨0⟩) (v := i32 0) rfl)))
  have last := first.tail (edge (.numeric (rest := [])
    (.get (stack := [i64 7, i64 42, i32 0]) (i := ⟨4⟩) (v := i64 0) rfl)))
  exact (last.tail (edge (.leaveValues alternateLocals alternateResults))).tail
    (edge (.leaveFrame alternateLocals (.values alternateResults) rfl))

-- The alternate arm completes without a native table and leaves the
-- i64 local at zero. The skipped arm would divide by zero.
example : (coreConditional conditional false).tables = [] := rfl
example : (limeConditional conditional false).tables = [] := rfl

example : Core.Steps spec noHost (coreSource (coreConditional conditional false) outer ⟨0⟩ (args 0 1))
    ⟨coreConditional conditional false, outer.toCore, coreValues alternateResults⟩ :=
  (Conditional.core_alternate_run (conditionReady 0 1) rfl rfl rfl (coreLinks conditional false)).mpr
    (.inr ⟨_, alternateFinished, .done rfl, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeSource (limeConditional conditional false) outer ⟨0⟩ (args 0 1))
    ⟨limeConditional conditional false, outer, Lime1.Execution.values alternateResults⟩ :=
  (Conditional.lime_alternate_run (conditionReady 0 1) rfl rfl rfl (limeLinks conditional false)).mpr
    (.inr ⟨_, alternateFinished, .done rfl, rfl⟩)

example : Core.Steps spec noHost (coreSource (coreConditional conditional false) outer ⟨0⟩ (args 0 0))
    (entry.coreCleanup (coreConditional conditional false) outer (entry.frame (args 0 0))
      (.label [] (middleBlock.tail.map Graph.coreEmit) [⟨1, [i64 7], outerBlock.tail.map Graph.coreEmit⟩])) :=
  (Conditional.core_operand_trap (conditionReady 0 0) rfl rfl rfl zeroTrace).mpr
    (.inr ⟨_, twoExits Graph.coreEmit (i64 42) [] _, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeSource (limeConditional conditional false) outer ⟨0⟩ (args 0 0))
    ⟨limeConditional conditional false, outer, [.trap]⟩ :=
  (Conditional.lime_operand_trap (conditionReady 0 0) rfl rfl rfl zeroTrace).mpr
    (.inr ⟨.done, unwind Graph.limeEmit (i64 42) [] _, rfl⟩)

private def trueSite : Conditional.Entry := { conditional with condition := ⟨0⟩, siteOnTrue := true }

private theorem trueReady : trueSite.Checked program tables outer ⟨0⟩ (args 91 1) :=
  ⟨rfl, rfl, rfl, rfl⟩

example : Core.Steps spec noHost (coreSource (coreConditional trueSite true) outer ⟨0⟩ (args 91 1))
    ⟨coreConditional trueSite true, outer.toCore, [.trap]⟩ :=
  (Conditional.core_lookup_trap trueReady rfl rfl rfl (ready 1)
    (coreTables trueSite) (coreTargets trueSite 1) rfl .null).mpr
      (.inr ⟨.done, unwind Graph.coreEmit (i64 42) [i32 5] _, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (limeSource (limeConditional trueSite true) outer ⟨0⟩ (args 91 1))
    ⟨limeConditional trueSite true, outer, [.trap]⟩ :=
  (Conditional.lime_lookup_trap trueReady rfl rfl rfl (ready 1)
    (limeTables trueSite) (limeTargets trueSite 1) rfl .null).mpr
      (.inr ⟨.done, unwind Graph.limeEmit (i64 42) [i32 5] _, rfl⟩)

end ConditionalFixture

namespace ControlFixture

private def outerChoice : Control.Choice := ⟨⟨3⟩, [.numeric (.get ⟨2⟩)], true⟩
private def innerChoice : Control.Choice := ⟨⟨1⟩, [.numeric (.get ⟨1⟩)], false⟩
private def middle : Control.Node := ⟨middleBlock, none⟩
private def inner : Control.Node := ⟨innerBlock, some innerChoice⟩

private def control : Control.Entry :=
  ⟨cont.address, cont.owner, cont.code, entry.op, entry.before, [⟨outerBlock, some outerChoice⟩, middle, inner]⟩

private theorem readyControl (divisor selected : BitVec 32) :
    control.Checked program tables outer ⟨0⟩ (args divisor selected) :=
  ⟨rfl, rfl, rfl, rfl⟩

example : control.site = entry := rfl
example : { control with nodes := [⟨outerBlock, some outerChoice⟩, middle,
    ⟨innerBlock, some { innerChoice with alternate := [.numeric (.get ⟨2⟩)] }⟩] }.check
    program tables = false := rfl

private def toInner : List Control.Position :=
  [.pending [] control.nodes, .test [] outerBlock outerChoice [middle, inner] 455,
   .pending [] [⟨outerBlock, none⟩, middle, inner],
   .pending [outerBlock] [middle, inner], .pending [outerBlock, middleBlock] [inner]]

private def toSite : List Control.Position :=
  toInner ++ [.test [outerBlock, middleBlock] innerBlock innerChoice [] 0,
    .pending [outerBlock, middleBlock] [⟨innerBlock, none⟩]]

private def toAlternate : List Control.Position :=
  toInner ++ [.test [outerBlock, middleBlock] innerBlock innerChoice [] 1]

private theorem sitePath (divisor : BitVec 32) :
    control.Trace (args divisor 0) toSite (.site cont.blocks) :=
  .taken rfl rfl (.block (.block (.taken rfl rfl (.block (.done _)))))

private theorem alternatePath :
    control.Trace (args 0 1) toAlternate
      (.alternate [outerBlock, middleBlock] (Control.Node.alternateCode innerBlock innerChoice)) :=
  .taken rfl rfl (.block (.block (.alternate rfl rfl)))

example : ∃ path last, control.Trace (args 0 1) path last := Control.trace_exists (readyControl 0 1)

private def coreControl (hasTable : Bool) : Core.Store Unit :=
  { coreStore with
    funcs := [callee.coreInstance, control.coreInstance]
    tables := if hasTable then coreStore.tables else [] }

private def limeControl (hasTable : Bool) : Lime1.Execution.Store Unit :=
  { limeStore with
    funcs := [.wasm callee.declaration.type callee.declaration.module callee.limeFunc, control.limeInstance]
    tables := if hasTable then limeStore.tables else [] }

private theorem coreLinks (hasTable : Bool) : program.CoreLinksAllocated (coreControl hasTable) := by
  intro _ _ found target used
  rw [noDirectTargets found] at used
  cases used

private theorem limeLinks (hasTable : Bool) : program.LimeLinksAllocated (limeControl hasTable) := by
  intro _ _ found target used
  rw [noDirectTargets found] at used
  cases used

private theorem coreTargets : (active 0).binding.site.CoreAllocated program (coreControl true) := by
  intro address fn used found
  obtain rfl := tableTarget used
  obtain rfl := Option.some.inj found.symm
  rfl

private theorem limeTargets : (active 0).binding.site.LimeAllocated program (limeControl true) := by
  intro address fn used found
  obtain rfl := tableTarget used
  obtain rfl := Option.some.inj found.symm
  rfl

example : Core.Steps spec noHost (coreSource (coreControl true) outer ⟨0⟩ (args 91 0))
    ⟨coreControl true, outer.toCore, coreValues results⟩ :=
  (Control.core_site_run (s := coreControl true) (readyControl 91 0) rfl (sitePath 91) (ready 0)
    (coreAllocated 0).tables coreTargets (coreLinks true) invoked).mpr
      (.inr ⟨_, finished, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource (limeControl true) outer ⟨0⟩ (args 91 0))
    ⟨limeControl true, outer, Lime1.Execution.values results⟩ :=
  (Control.lime_site_run (s := limeControl true) (readyControl 91 0) rfl (sitePath 91) (ready 0)
    (limeAllocated 0).tables limeTargets (limeLinks true) invoked).mpr
      (.inr ⟨_, finished, rfl⟩)

private def untouched : List Value := args 0 1 ++ [i64 0]
private def alternateUpdated : List Value := args 1 1 ++ [i64 0]
private def alternateResults : List Value := [i64 7, i64 0, i32 1, i64 0]

private theorem alternateFinished : program.FrameRuns ⟨1⟩
    (control.alternatePhase (args 0 1) [outerBlock, middleBlock] (Control.Node.alternateCode innerBlock innerChoice))
    (.done (.values alternateResults)) := by
  have edge {a b : Graph.Phase} :=
    (program.frameEdge_iff (a := a) (b := b) (fn := owner) (address := ⟨1⟩) rfl).mpr
  have enter := Relation.ReflTransGen.single (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail
      (.blockEnter untouched [] innerBlock.result innerChoice.alternate innerBlock.tail))))
  have read := enter.tail (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail (.blockStep [] innerBlock.result innerBlock.tail
      (.numeric (rest := []) (.get (stack := []) (i := ⟨1⟩) (v := i32 1) (locals := untouched) rfl))))))
  have leaveInner := read.tail (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail (.blockStep [] innerBlock.result innerBlock.tail
      (.leaveValues untouched [i32 1])))))
  have readZero := leaveInner.tail (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail (.numeric (locals := untouched)
      (rest := [.numeric (.bin .i32 .add)]) (.get (stack := [i32 1]) (i := ⟨0⟩) (v := i32 0) rfl)))))
  have add := readZero.tail (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail (.numeric (locals := untouched) (rest := [])
      (.bin (stack := []) (x := 1) (y := 0) (z := 1) (op := .add) rfl)))))
  have leaveMiddle := add.tail (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.blockStep [] middleBlock.result middleBlock.tail (.leaveValues untouched [i32 1]))))
  have setLocal := Locals.fact (.set untouched ⟨0⟩ (i32 1) (by decide))
  have assign := leaveMiddle.tail (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.localSet (saved := []) (rest := [.numeric (.get ⟨4⟩)]) setLocal)))
  have readResult := assign.tail (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.numeric (rest := []) (.get (stack := []) (i := ⟨4⟩) (v := i64 0) (locals := alternateUpdated) rfl))))
  have leaveOuter := readResult.tail (edge (.blockStep [i64 7] outerBlock.result outerBlock.tail
    (.leaveValues alternateUpdated [i64 0])))
  have first := leaveOuter.tail (edge (.numeric (locals := alternateUpdated) (rest := [.numeric (.get ⟨4⟩)])
    (.get (stack := [i64 7, i64 0]) (i := ⟨0⟩) (v := i32 1) rfl)))
  have last := first.tail (edge (.numeric (rest := [])
    (.get (stack := [i64 7, i64 0, i32 1]) (i := ⟨4⟩) (v := i64 0) rfl)))
  exact (last.tail (edge (.leaveValues alternateUpdated alternateResults))).tail
    (edge (.leaveFrame alternateUpdated (.values alternateResults) rfl))

-- The inner alternate returns into already-entered blocks. The remaining
-- tails update local zero and preserve the default i64, without a table.
example : (coreControl false).tables = [] := rfl
example : (limeControl false).tables = [] := rfl

example : Core.Steps spec noHost (coreSource (coreControl false) outer ⟨0⟩ (args 0 1))
    ⟨coreControl false, outer.toCore, coreValues alternateResults⟩ :=
  (Control.core_alternate_run (readyControl 0 1) rfl alternatePath (coreLinks false)).mpr
    (.inr ⟨_, alternateFinished, .done rfl, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource (limeControl false) outer ⟨0⟩ (args 0 1))
    ⟨limeControl false, outer, Lime1.Execution.values alternateResults⟩ :=
  (Control.lime_alternate_run (readyControl 0 1) rfl alternatePath (limeLinks false)).mpr
    (.inr ⟨_, alternateFinished, .done rfl, rfl⟩)

-- Choosing the site with zero divisor reaches the intermediate native
-- unwind after two label exits. The outer label and its saved i64 remain.
example : Core.Steps spec noHost (coreSource (coreControl false) outer ⟨0⟩ (args 0 0))
    (entry.coreCleanup (coreControl false) outer (entry.frame (args 0 0))
      (.label [] (middleBlock.tail.map Graph.coreEmit) [⟨1, [i64 7], outerBlock.tail.map Graph.coreEmit⟩])) :=
  (Control.core_operand_trap (readyControl 0 0) rfl (sitePath 0) zeroTrace).mpr
    (.inr ⟨_, twoExits Graph.coreEmit (i64 42) [] _, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource (limeControl false) outer ⟨0⟩ (args 0 0))
    (entry.limeCleanup (limeControl false) outer (entry.frame (args 0 0))
      (.label [] (middleBlock.tail.map Graph.limeEmit) [⟨1, [i64 7], outerBlock.tail.map Graph.limeEmit⟩])) :=
  (Control.lime_operand_trap (readyControl 0 0) rfl (sitePath 0) zeroTrace).mpr
    (.inr ⟨_, twoExits Graph.limeEmit (i64 42) [] _, rfl⟩)

end ControlFixture
