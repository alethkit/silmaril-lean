import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame FuncAddr Value)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallResolution
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
private def callerType : V1.FuncType := ⟨[.int .i32, .int .i32], [.int .i64, .int .i32, .int .i64, .int .i32]⟩
private def mismatchType : V1.FuncType := ⟨[], []⟩
private def readLocal (i : LocalIdx) : Graph.Op := .numeric (.get i)
private def returning : Graph.Function :=
  ⟨⟨{ types := [signature] }, ⟨0⟩, signature.params, [], signature.results⟩, 0, [], [readLocal ⟨1⟩, readLocal ⟨0⟩]⟩
private def selfDecl : Declaration :=
  ⟨{ types := [signature], funcs := [⟨1⟩] }, ⟨0⟩, signature.params, [], signature.results⟩
private def self : CallTarget := ⟨⟨0⟩, ⟨1⟩, selfDecl⟩
private def recursive : Graph.Function := ⟨selfDecl, 0, [i64 42, i32 5], [.call self]⟩
private def owner : Graph.Function :=
  ⟨⟨{ types := [callerType, signature], tables := [⟨1⟩] }, ⟨0⟩, callerType.params, [.int .i64], callerType.results⟩,
    0, [i64 7, i64 42, i32 455], [.unreachable]⟩
private def mismatch : Graph.Function :=
  ⟨⟨{ types := [mismatchType] }, ⟨0⟩, mismatchType.params, [], mismatchType.results⟩, 0, [], []⟩

private def functions : List Graph.Function := [returning, recursive, owner, mismatch]
private def program : Graph.Program := ⟨functions.map some⟩
private def divide : Prefix.Op := .bin .i32 (.div .unsigned)
private def selector : Prefix.Op := .get ⟨1⟩
private def entry : GraphEntry.Entry :=
  ⟨⟨⟨2⟩, owner, [readLocal ⟨0⟩], none⟩, ⟨⟨1⟩, signature⟩, [.get ⟨0⟩, divide, selector]⟩
private def outer : Frame := ⟨[i32 77], { funcs := [⟨0⟩, ⟨2⟩] }⟩
private def args : List Value := [i32 91, i32 0]
private def nullArgs : List Value := [i32 91, i32 1]
private def zeroArgs : List Value := [i32 0, i32 0]
private def inner : Frame := owner.declaration.frame args
private def tables (refs : List (Option FuncAddr)) : Source.Tables := [⟨[], none⟩, ⟨refs, some 1⟩]
private def active (refs : List (Option FuncAddr)) (selected : BitVec 32 := 0) : Source.Activation :=
  ⟨owner.declaration.frame [i32 91, i32 selected], ⟨⟨1⟩, ⟨⟨refs, some 1⟩, ⟨1⟩, signature⟩⟩,
    ⟨[i64 7], [i64 42, i32 5], selected⟩⟩

private def returnRefs : List (Option FuncAddr) := [some ⟨0⟩, none]
private def recurseRefs : List (Option FuncAddr) := [some ⟨1⟩]
private def mismatchRefs : List (Option FuncAddr) := [some ⟨3⟩]

private def states (divisor : BitVec 32) : List OperandState :=
  [(owner.initial, entry.before), (owner.initial ++ [i32 divisor], [divide, selector])]

private def normalStates : List OperandState := states 91 ++ [([i64 7, i64 42, i32 5], [selector])]
private def lookupStack (selected : BitVec 32) : List Value := [i64 7, i64 42, i32 5, i32 selected]

private theorem normalTrace (selected : BitVec 32) :
    entry.OperandTrace [i32 91, i32 selected] normalStates (.values (lookupStack selected)) :=
  .value (.get rfl) (.value (.bin (stack := [i64 7, i64 42]) (x := 455) (y := 91) rfl)
    (.value (.get rfl) (.done _)))

private theorem zeroTrace : entry.OperandTrace zeroArgs (states 0) (.trap [i64 7, i64 42] [selector]) :=
  .value (.get rfl) (.trap (.trap (stack := [i64 7, i64 42]) (x := 455) (y := 0)
    (cause := .divideByZero) rfl))

private theorem returnReady : entry.AtSite program (tables returnRefs) outer ⟨1⟩ args
    normalStates (lookupStack 0) (active returnRefs) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, normalTrace 0, rfl⟩
private theorem recurseReady : entry.AtSite program (tables recurseRefs) outer ⟨1⟩ args
    normalStates (lookupStack 0) (active recurseRefs) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, normalTrace 0, rfl⟩
private theorem boundsReady : entry.AtSite program (tables []) outer ⟨1⟩ args
    normalStates (lookupStack 0) (active []) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, normalTrace 0, rfl⟩
private theorem nullReady : entry.AtSite program (tables returnRefs) outer ⟨1⟩ nullArgs
    normalStates (lookupStack 1) (active returnRefs 1) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, normalTrace 1, rfl⟩
private theorem mismatchReady : entry.AtSite program (tables mismatchRefs) outer ⟨1⟩ args
    normalStates (lookupStack 0) (active mismatchRefs) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, normalTrace 0, rfl⟩

example : entry.check program (tables [some ⟨99⟩]) = false := rfl
example : { entry with before := [.get ⟨9⟩] }.check program (tables returnRefs) = false := rfl
example : entry.prepare program [⟨returnRefs, none⟩] args (lookupStack 0) = none := rfl
example : entry.prepare program (tables returnRefs) [i64 91] (lookupStack 0) = none := rfl
example : (active []).resolve program = some .bounds := rfl
example : (active returnRefs).resolve program = some (.resolved ⟨0⟩) := rfl
example : (active returnRefs 1).resolve program = some .null := rfl
example : (active mismatchRefs).resolve program = some (.mismatch ⟨3⟩) := rfl
example : ∃ prepared, entry.prepare program (tables returnRefs) args (lookupStack 0) = some prepared :=
  prepare_exists returnReady.checked returnReady.trace
example : inner.locals = [i32 91, i32 0, i64 0] := rfl

private def coreStore (refs : List (Option FuncAddr)) : Core.Store Unit :=
  { funcs := [returning.coreInstance, recursive.coreInstance, entry.coreInstance, mismatch.coreInstance]
    tables := (tables refs).map Runtime.TableInst.toCore }
private def limeStore (refs : List (Option FuncAddr)) : Lime1.Execution.Store Unit :=
  { funcs := [returning, recursive].map (fun fn => .wasm fn.declaration.type fn.declaration.module fn.limeFunc) ++
      [entry.limeInstance, .wasm mismatch.declaration.type mismatch.declaration.module mismatch.limeFunc]
    tables := tables refs }

private theorem coreDirect {refs : List (Option FuncAddr)} {addr : FuncAddr} {fn : Graph.Function}
    (found : program.lookup addr = some fn) (other : addr ≠ ⟨2⟩) :
    (coreStore refs).funcs[addr.value]? = some fn.coreInstance := by
  rcases addr with ⟨_ | _ | _ | _ | n⟩
  · obtain rfl := Option.some.inj found.symm
    rfl
  · obtain rfl := Option.some.inj found.symm
    rfl
  · exact (other rfl).elim
  · obtain rfl := Option.some.inj found.symm
    rfl
  · cases found

private theorem limeDirect {refs : List (Option FuncAddr)} {addr : FuncAddr} {fn : Graph.Function}
    (found : program.lookup addr = some fn) (other : addr ≠ ⟨2⟩) :
    (limeStore refs).funcs[addr.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.limeFunc) := by
  rcases addr with ⟨_ | _ | _ | _ | n⟩
  · obtain rfl := Option.some.inj found.symm
    rfl
  · obtain rfl := Option.some.inj found.symm
    rfl
  · exact (other rfl).elim
  · obtain rfl := Option.some.inj found.symm
    rfl
  · cases found

private theorem targetAddress {addr : FuncAddr} {fn : Graph.Function} {target : CallTarget}
    (found : program.lookup addr = some fn) (used : target ∈ fn.targets) :
    target.address ≠ ⟨2⟩ := by
  have member : fn ∈ functions := by
    cases slot : functions[addr.value]? with
    | none => simp [Graph.Program.lookup, program, List.getElem?_map, slot] at found
    | some f =>
      have eq : f = fn := by
        simpa [Graph.Program.lookup, program, List.getElem?_map, slot] using found
      exact eq ▸ List.mem_of_getElem? slot
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simp [Graph.Function.targets, returning, readLocal, Graph.codeTargets, Graph.Op.targets] at used
  · have eq : target = self := by
      simpa [Graph.Function.targets, recursive, Graph.codeTargets, Graph.Op.targets] using used
    subst target
    decide
  · simp [Graph.Function.targets, owner, Graph.codeTargets, Graph.Op.targets] at used
  · simp [Graph.Function.targets, mismatch, Graph.codeTargets] at used

private theorem coreAllocated {refs : List (Option FuncAddr)} {selected : BitVec 32} (avoids : some ⟨2⟩ ∉ refs) :
    entry.CoreAllocated program (tables refs) (active refs selected) (coreStore refs) :=
  ⟨rfl, fun _ _ found _ used _ child => coreDirect child (targetAddress found used),
    fun _ _ found => by simp [coreStore, List.getElem?_map, found],
    fun _ _ member found => coreDirect found (by rintro rfl; exact avoids member)⟩

private theorem limeAllocated {refs : List (Option FuncAddr)} {selected : BitVec 32} (avoids : some ⟨2⟩ ∉ refs) :
    entry.LimeAllocated program (tables refs) (active refs selected) (limeStore refs) :=
  ⟨rfl, fun _ _ found _ used _ child => limeDirect child (targetAddress found used),
    fun _ _ found => found,
    fun _ _ member found => limeDirect found (by rintro rfl; exact avoids member)⟩

-- The allocated code at the graph address is the indirect body.
example : (coreStore returnRefs).funcs[2]? = some entry.coreInstance := rfl
example : (limeStore returnRefs).funcs[2]? = some entry.limeInstance := rfl
example : entry.coreFunc.body =
    [Instr.intConst .i64 7, Instr.intConst .i64 42, Instr.intConst .i32 455,
      .localGet ⟨0⟩, .intBinOp .i32 (.div .unsigned), .localGet ⟨1⟩, .callIndirect tableIndex ⟨1⟩, .localGet ⟨0⟩] := rfl

private def returnedCall : Context.Invocation :=
  ⟨(active returnRefs).binding.site, inner, 0, [i64 7], [i64 42, i32 5], ⟨0⟩, returning⟩
private def recursiveCall : Context.Invocation :=
  ⟨(active recurseRefs).binding.site, inner, 0, [i64 7], [i64 42, i32 5], ⟨1⟩, recursive⟩
private theorem returnedInvoked : (active returnRefs).invocation program = some returnedCall := rfl
private theorem recursiveInvoked : (active recurseRefs).invocation program = some recursiveCall := rfl

example : (entry.corePrefix (coreStore returnRefs) outer ⟨1⟩ args (active returnRefs) (.resolved ⟨0⟩) normalStates).length = 9 := rfl
example : (entry.limePrefix (limeStore returnRefs) outer ⟨1⟩ args (active returnRefs) (.resolved ⟨0⟩) normalStates).length = 7 := rfl
example := GraphEntry.core_prefix_exact (P := spec) returnReady (coreAllocated (by decide))
  (out := .resolved ⟨0⟩) rfl
example := GraphEntry.lime_prefix_exact returnReady (limeAllocated (by decide))
  (out := .resolved ⟨0⟩) rfl

private theorem returnedPath : program.FrameRuns ⟨0⟩ returnedCall.entered (.done (.values [i32 5, i64 42])) := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) (fn := returning)
    (address := ⟨0⟩) rfl).mpr
  have first := Relation.ReflTransGen.single (edge (.numeric (locals := [i64 42, i32 5])
    (rest := [readLocal ⟨0⟩]) (.get (stack := []) (i := ⟨1⟩) (v := i32 5) rfl)))
  have second := first.tail (edge (.numeric (rest := []) (.get (stack := [i32 5]) (i := ⟨0⟩) (v := i64 42) rfl)))
  exact (second.tail (edge (.leaveValues [i64 42, i32 5] [i32 5, i64 42]))).tail
    (edge (.leaveFrame _ (.values [i32 5, i64 42]) rfl))

private def results : List Value := [i64 7, i32 5, i64 42, i32 91]

private theorem finished : Context.Resume.Runs program returnedCall entry.cont (.callee returnedCall.entered)
    (.caller (.done (.values results))) := by
  have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) returnReady.checked.found).mpr
  have before := Context.Resume.of_callee_run (cont := entry.cont) (resume_guard returnReady returnedInvoked).1 returnedPath
  have resumed := before.tail (.resume (edge (.numeric (locals := inner.locals) (rest := [])
    (.get (stack := [i64 7, i32 5, i64 42]) (i := ⟨0⟩) (v := i32 91) rfl))))
  exact (resumed.tail (.caller (edge (.leaveValues inner.locals results)))).tail
    (.caller (edge (.leaveFrame inner.locals (.values results) rfl)))

example : Core.Steps spec noHost (GraphEntry.coreSource (coreStore returnRefs) outer ⟨1⟩ args)
    ⟨coreStore returnRefs, outer.toCore, coreValues results⟩ :=
  (GraphEntry.core_run_iff returnReady (coreAllocated (by decide)) returnedInvoked).mpr
    (.inr ⟨_, finished, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost (GraphEntry.limeSource (limeStore returnRefs) outer ⟨1⟩ args)
    ⟨limeStore returnRefs, outer, Lime1.Execution.values results⟩ :=
  (GraphEntry.lime_run_iff returnReady (limeAllocated (by decide)) returnedInvoked).mpr
    (.inr ⟨_, finished, rfl⟩)

private theorem cleanup {A : Type} (rest : List A) :
    CleanupRuns (.label [i64 7, i64 42, i32 5] rest) .done := by
  have discard : Prefix.Discard [i64 7, i64 42, i32 5] rest [] [] := by
    simpa only [List.nil_append, List.append_nil] using (Prefix.Discard.cut [] [i64 7, i64 42, i32 5] rest [] (.inl (by simp)))
  exact ((Relation.ReflTransGen.single (.discard discard)).tail .label).tail .frame

example : Core.Steps spec noHost (GraphEntry.coreSource (coreStore []) outer ⟨1⟩ args)
    ⟨coreStore [], outer.toCore, [.trap]⟩ :=
  (GraphEntry.core_trap_run_iff boundsReady (coreAllocated (by decide)) rfl .bounds).mpr
    (.inr ⟨.done, cleanup _, rfl⟩)

-- The bounds trap can discard just the cast while retaining the stack,
-- the pending call_ref, and the caller's local-read continuation.
example : Core.Steps spec noHost (GraphEntry.coreSource (coreStore []) outer ⟨1⟩ args)
    (entry.coreCleanup (coreStore []) outer inner
      (.label [i64 7, i64 42, i32 5] [(active []).binding.site.coreCall, .plain (.localGet ⟨0⟩)])) := by
  let site := (active []).binding.site
  have cut : Prefix.Discard [i64 7, i64 42, i32 5] [site.coreCast, site.coreCall, .plain (.localGet ⟨0⟩)]
      [i64 7, i64 42, i32 5] [site.coreCall, .plain (.localGet ⟨0⟩)] := by
    simpa only [List.append_nil, List.singleton_append] using
      (Prefix.Discard.cut [i64 7, i64 42, i32 5] [] [site.coreCast] [site.coreCall, .plain (.localGet ⟨0⟩)]
        (.inr (by simp)))
  exact (GraphEntry.core_trap_run_iff boundsReady (coreAllocated (by decide)) rfl .bounds).mpr
    (.inr ⟨_, Relation.ReflTransGen.single (.discard cut), rfl⟩)

example : Core.Steps spec noHost (GraphEntry.coreSource (coreStore mismatchRefs) outer ⟨1⟩ args)
    ⟨coreStore mismatchRefs, outer.toCore, [.trap]⟩ :=
  (GraphEntry.core_trap_run_iff mismatchReady (coreAllocated (by decide)) rfl (.mismatch ⟨3⟩)).mpr
    (.inr ⟨.done, cleanup _, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost (GraphEntry.limeSource (limeStore returnRefs) outer ⟨1⟩ nullArgs)
    ⟨limeStore returnRefs, outer, [.trap]⟩ :=
  (GraphEntry.lime_trap_run_iff nullReady (limeAllocated (by decide)) rfl .null).mpr
    (.inr ⟨.done, cleanup _, rfl⟩)

example : Core.Steps spec noHost (GraphEntry.coreSource (coreStore returnRefs) outer ⟨1⟩ nullArgs)
    ⟨coreStore returnRefs, outer.toCore, [.trap]⟩ :=
  (GraphEntry.core_trap_run_iff nullReady (coreAllocated (by decide)) rfl .null).mpr
    (.inr ⟨.done, cleanup _, rfl⟩)

-- The dividend and divisor are on the stack, with the indirect instruction still pending.
example : Core.Steps spec noHost (GraphEntry.coreSource (coreStore returnRefs) outer ⟨1⟩ args)
    (entry.coreOperands (coreStore returnRefs) outer args
      ([i64 7, i64 42, i32 455, i32 91], [divide, selector])) :=
  (GraphEntry.core_run_iff returnReady (coreAllocated (by decide)) returnedInvoked).mpr
    (.inl (.tail _ (.tail _ (.tail _ (.head _)))))

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (GraphEntry.limeSource (limeStore returnRefs) outer ⟨1⟩ args)
    (entry.limeOperands (limeStore returnRefs) outer args
      ([i64 7, i64 42, i32 455, i32 91], [divide, selector])) :=
  (GraphEntry.lime_run_iff returnReady (limeAllocated (by decide)) returnedInvoked).mpr
    (.inl (.tail _ (.tail _ (.tail _ (.head _)))))

private theorem zeroReady : entry.Checked program (tables returnRefs) outer ⟨1⟩ zeroArgs :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem cleanupBeforeLookup {A : Type} (rest : List A) :
    CleanupRuns (.label [i64 7, i64 42] rest) .done := by
  have discard : Prefix.Discard [i64 7, i64 42] rest [] [] := by
    simpa only [List.nil_append, List.append_nil] using
      (Prefix.Discard.cut [] [i64 7, i64 42] rest [] (.inl (by simp)))
  exact ((Relation.ReflTransGen.single (.discard discard)).tail .label).tail .frame

-- The prefix failure requires only the entry's function allocation. The store has no table.
private def coreNoTable := { coreStore returnRefs with tables := [] }
private def limeNoTable := { limeStore returnRefs with tables := [] }

example : Core.Steps spec noHost (GraphEntry.coreSource coreNoTable outer ⟨1⟩ zeroArgs)
    (entry.coreCleanup coreNoTable outer (entry.frame zeroArgs) (.label [i64 7, i64 42]
      [.plain (.localGet ⟨1⟩), .plain (.callIndirect tableIndex ⟨1⟩), .plain (.localGet ⟨0⟩)])) :=
  (GraphEntry.core_operand_trap_run_iff zeroReady rfl zeroTrace).mpr
    (.inr ⟨_, .refl, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (GraphEntry.limeSource limeNoTable outer ⟨1⟩ zeroArgs)
    (entry.limeCleanup limeNoTable outer (entry.frame zeroArgs) (.label [i64 7, i64 42]
      [.source (.localGet ⟨1⟩), .source (.callIndirect ⟨1⟩), .source (.localGet ⟨0⟩)])) :=
  (GraphEntry.lime_operand_trap_run_iff zeroReady rfl zeroTrace).mpr
    (.inr ⟨_, .refl, rfl⟩)

example : Core.Steps spec noHost (GraphEntry.coreSource coreNoTable outer ⟨1⟩ zeroArgs)
    ⟨coreNoTable, outer.toCore, [.trap]⟩ :=
  (GraphEntry.core_operand_trap_run_iff zeroReady rfl zeroTrace).mpr
    (.inr ⟨.done, cleanupBeforeLookup _, rfl⟩)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (GraphEntry.limeSource limeNoTable outer ⟨1⟩ zeroArgs) ⟨limeNoTable, outer, [.trap]⟩ :=
  (GraphEntry.lime_operand_trap_run_iff zeroReady rfl zeroTrace).mpr
    (.inr ⟨.done, cleanupBeforeLookup _, rfl⟩)

private def deep : Nat → Graph.Phase
  | 0 => recursiveCall.entered
  | n + 1 => .label [i64 42, i32 5] (.active [] self (deep n) [])

private theorem deepActive (n : Nat) : (deep n).Active := by cases n <;> trivial
private theorem selfUsed : self ∈ recursive.targets := by
  simp [recursive, Graph.Function.targets, Graph.codeTargets, Graph.Op.targets]

private theorem deeper (n : Nat) : program.FrameRuns ⟨1⟩ (deep n) (deep (n + 1)) := by
  induction n with
  | zero =>
    have edge {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) (address := ⟨1⟩)
      (fn := recursive) rfl).mpr
    exact (Relation.ReflTransGen.single (edge (.dispatch [i64 42, i32 5] [] [i64 42, i32 5] self [] selfUsed rfl))).tail
      (edge (.child [i64 42, i32 5] [] self [] (a := .invoke [i64 42, i32 5]) (b := deep 0) selfUsed trivial
        (edge (.enter [i64 42, i32 5] rfl))))
  | succ n ih =>
    exact program.frame_lift_child (fn := recursive) (address := ⟨1⟩) rfl selfUsed (deepActive n)
      (locals := [i64 42, i32 5]) (saved := []) (rest := []) ih

private theorem recursivePrefix (n : Nat) : program.FrameRuns ⟨1⟩ recursiveCall.entered (deep n) := by
  induction n with
  | zero => exact .refl
  | succ n ih => exact ih.trans (deeper n)

example (n : Nat) : Core.Steps spec noHost (GraphEntry.coreSource (coreStore recurseRefs) outer ⟨1⟩ args)
    (entry.cont.coreConfig recursiveCall (coreStore recurseRefs) outer (.callee (deep n))) :=
  (GraphEntry.core_run_iff recurseReady (coreAllocated (by decide)) recursiveInvoked).mpr
    (.inr ⟨_, Context.Resume.of_callee_run (resume_guard recurseReady recursiveInvoked).1 (recursivePrefix n), rfl⟩)

example (n : Nat) : Lime1.Execution.Steps CallFrame.limeNoHost (GraphEntry.limeSource (limeStore recurseRefs) outer ⟨1⟩ args)
    (entry.cont.limeConfig recursiveCall (limeStore recurseRefs) outer (.callee (deep n))) :=
  (GraphEntry.lime_run_iff recurseReady (limeAllocated (by decide)) recursiveInvoked).mpr
    (.inr ⟨_, Context.Resume.of_callee_run (resume_guard recurseReady recursiveInvoked).1 (recursivePrefix n), rfl⟩)

example (n : Nat) : ((deep n).frames ⟨1⟩).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((deep n).frames ⟨1⟩).length + 1 = n + 1 + 1
    rw [ih]
