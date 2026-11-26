import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame FuncAddr Value)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume
open Silmaril.Wasm.Institution.Operational.CallContinuation
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private abbrev spec := Numerics.Profile.spec
private abbrev t32 : NumType := .int .i32
private abbrev t64 : NumType := .int .i64

private def signature : V1.FuncType := ⟨[], [t64, t32]⟩
private def callerType : V1.FuncType := ⟨[t32, t32, t32, t64, t32, t32], [t64, t32, t64, t32, t32]⟩
private def calleeDecl : Declaration :=
  ⟨{ types := [signature] }, ⟨0⟩, signature.params, [], signature.results⟩
private def returned : List Value := [i64 700, i32 71]
private def good : Graph.Function := ⟨calleeDecl, 0, returned, []⟩
private def raises : Graph.Function := ⟨calleeDecl, 0, [], [.unreachable]⟩
private def owner : Graph.Function :=
  ⟨⟨{ types := [callerType, signature], tables := [⟨0⟩] }, ⟨0⟩, callerType.params, [], callerType.results⟩,
    0, [i64 42], [.unreachable]⟩
private def program : Graph.Program := ⟨[some good, some raises, some owner]⟩
private def refs : List (Option FuncAddr) := [some ⟨0⟩, none, some ⟨1⟩]
private def tables : Source.Tables := [⟨refs, some 3⟩]
private def outer : Frame := ⟨[i32 77], { funcs := [⟨2⟩] }⟩
private def args (restart selector : BitVec 32) : List Value := [i32 restart, i32 0, i32 1, i64 21, i32 22, i32 selector]
private def indices : List LocalIdx := [⟨4⟩, ⟨3⟩, ⟨5⟩]
private def entry : Loop.Entry :=
  { address := ⟨2⟩, owner, result := none, restart := ⟨0⟩, nextRestart := ⟨1⟩,
    branchTypes := [], choose := ⟨2⟩, op := ⟨⟨1⟩, signature⟩, before := [.get ⟨4⟩, .get ⟨5⟩],
    insideTail := indices.map Graph.Op.set,
    tail := [.numeric (.get ⟨4⟩), .numeric (.get ⟨3⟩), .numeric (.get ⟨5⟩), .numeric (.get ⟨0⟩)] }

private theorem checked (selector : BitVec 32) : entry.Checked program tables outer ⟨0⟩ (args 1 selector) :=
  ⟨rfl, rfl, rfl, rfl⟩

example : { entry with insideTail := [.set ⟨3⟩, .set ⟨4⟩, .set ⟨5⟩] }.check program tables = false := rfl

private theorem trip (restart selector : BitVec 32) :
    Loop.Runs entry ⟨args restart selector, .enter⟩
      ⟨args 0 selector, if restart = 0 then .readChoice else .branch⟩ := by
  have write := Locals.fact (.set (args restart selector) entry.restart (i32 0) (by change 0 < 6; decide))
  have read : Loop.Runs entry ⟨args restart selector, .enter⟩ ⟨args restart selector, .writeRestart restart 0⟩ :=
    ((Relation.ReflTransGen.single Loop.Edge.enter).tail (.readRestart rfl)).tail (.readNext rfl)
  exact (read.tail (.writeRestart write)).tail .testRestart

private theorem reachesSite (selector : BitVec 32) :
    Loop.Runs entry (entry.initial (args 1 selector)) ⟨args 0 selector, .site⟩ :=
  ((((trip 1 selector).tail .restart).trans (trip 0 selector)).tail (.readChoice rfl)
    |>.tail .testChoice).tail .enterSite

private def active (selector : BitVec 32) : Source.Activation :=
  ⟨entry.frame (args 0 selector), ⟨⟨0⟩, ⟨⟨refs, some 3⟩, ⟨1⟩, signature⟩⟩, ⟨[i32 22], [], selector⟩⟩
private theorem prepared (selector : BitVec 32) :
    entry.op.prepare program tables (entry.frame (args 0 selector)) [i32 22, i32 selector] =
      some (active selector) := rfl
private theorem operands (selector : BitVec 32) :
    OperandTrace (args 0 selector) [] entry.before [([], entry.before), ([i32 22], [.get ⟨5⟩])]
      (.values [i32 22, i32 selector]) :=
  .value (.get rfl) (.value (.get rfl) (.done _))

private def success : Context.Invocation :=
  ⟨(active 0).binding.site, (active 0).caller, 0, [i32 22], [], ⟨0⟩, good⟩
private def failing : Context.Invocation :=
  ⟨(active 2).binding.site, (active 2).caller, 2, [i32 22], [], ⟨1⟩, raises⟩
private def writes (selector : BitVec 32) : Writes entry (active selector).operands.saved signature.results :=
  ⟨indices, rfl, rfl⟩

example : (active 0).invocation program = some success := rfl
example : (active 1).resolve program = some .null := rfl
example : (active 2).invocation program = some failing := rfl

private def coreStore : Core.Store Unit :=
  { funcs := [good.coreInstance, raises.coreInstance, entry.coreInstance], tables := tables.map Runtime.TableInst.toCore }
private def limeStore : Lime1.Execution.Store Unit :=
  { funcs := [.wasm calleeDecl.type calleeDecl.module good.limeFunc,
      .wasm calleeDecl.type calleeDecl.module raises.limeFunc, entry.limeInstance], tables }

private theorem noTargets (address : FuncAddr) (fn : Graph.Function)
    (found : program.lookup address = some fn) : fn.targets = [] := by
  rcases address with ⟨_ | _ | _ | _⟩ <;> first | cases found; rfl | cases found

private theorem coreLinks : program.CoreLinksAllocated coreStore :=
  fun a fn found _ used => (List.not_mem_nil (noTargets a fn found ▸ used)).elim
private theorem limeLinks : program.LimeLinksAllocated limeStore :=
  fun a fn found _ used => (List.not_mem_nil (noTargets a fn found ▸ used)).elim
private theorem coreTable : Source.Tables.CoreAllocated tables coreStore := by
  intro a table found
  simp [coreStore, List.getElem?_map, found]
private theorem limeTable : Source.Tables.LimeAllocated tables limeStore := fun _ _ found => found

private theorem usedAddr {addr : FuncAddr} (used : some addr ∈ refs) : addr = ⟨0⟩ ∨ addr = ⟨1⟩ := by
  simpa [refs] using used

private theorem coreTargets (selector : BitVec 32) : (active selector).binding.site.CoreAllocated program coreStore := by
  intro address fn used found
  rcases usedAddr used with rfl | rfl <;> cases found <;> rfl
private theorem limeTargets (selector : BitVec 32) : (active selector).binding.site.LimeAllocated program limeStore := by
  intro address fn used found
  rcases usedAddr used with rfl | rfl <;> cases found <;> rfl

private theorem calleeReturn : program.FrameRuns success.address success.entered (.done (.values returned)) := by
  have step {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) (fn := good) (address := ⟨0⟩) rfl).mpr
  exact (Relation.ReflTransGen.single (step (.leaveValues [] returned))).tail (step (.leaveFrame [] _ rfl))

private theorem calleeTrapUpToFrameExit :
    program.FrameRuns failing.address failing.entered (.exit [] .trap) := by
  have step {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) (fn := raises) (address := ⟨1⟩) rfl).mpr
  exact (Relation.ReflTransGen.single (step (.unreachable [] [] []))).tail (step (.leaveTrap []))

private theorem calleeTrap : program.FrameRuns failing.address failing.entered (.done .trap) :=
  calleeTrapUpToFrameExit.tail ((program.frameEdge_iff (fn := raises) rfl).mpr (.leaveFrame [] .trap trivial))

private def updated : List Value := [i32 0, i32 0, i32 1, i64 700, i32 71, i32 22]
private def result : List Value := [i64 42, i32 71, i64 700, i32 22, i32 0]

private theorem savedAndWritten {A : Type} (tail : List A) :
    Runs (delivery success.caller success.saved indices tail (.values returned)) (.caller updated false) := by
  let first : List Value := [i32 0, i32 0, i32 1, i64 21, i32 71, i32 0]
  let second : List Value := [i32 0, i32 0, i32 1, i64 700, i32 71, i32 0]
  have one : Edge (delivery success.caller success.saved indices tail (.values returned))
      (.write first [i32 22, i64 700] [⟨3⟩, ⟨5⟩]) :=
    .write rfl (Locals.fact (.set (args 0 0) ⟨4⟩ (i32 71) (by decide)))
  have two : Edge (A := A) (.write first [i32 22, i64 700] [⟨3⟩, ⟨5⟩])
      (.write second [i32 22] [⟨5⟩]) :=
    .write rfl (Locals.fact (.set first ⟨3⟩ (i64 700) (by decide)))
  have three : Edge (A := A) (.write second [i32 22] [⟨5⟩]) (.write updated [] []) :=
    .write rfl (Locals.fact (.set second ⟨5⟩ (i32 22) (by decide)))
  exact ((((Relation.ReflTransGen.single one).tail two).tail three).tail (.leaveArm updated)).tail
    (.leaveLoop updated false)

private theorem callerReturn : program.FrameRuns entry.address (entryPhase entry updated false) (.done (.values result)) := by
  have step {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) (fn := owner) (address := ⟨2⟩) rfl).mpr
  have one := Relation.ReflTransGen.single (step (.numeric (locals := updated) (rest := entry.tail.drop 1)
    (.get (stack := [i64 42]) (i := ⟨4⟩) (v := i32 71) rfl)))
  have two := one.tail (step (.numeric (rest := entry.tail.drop 2)
    (.get (stack := [i64 42, i32 71]) (i := ⟨3⟩) (v := i64 700) rfl)))
  have three := two.tail (step (.numeric (rest := entry.tail.drop 3)
    (.get (stack := [i64 42, i32 71, i64 700]) (i := ⟨5⟩) (v := i32 22) rfl)))
  have four := three.tail (step (.numeric (rest := [])
    (.get (stack := [i64 42, i32 71, i64 700, i32 22]) (i := ⟨0⟩) (v := i32 0) rfl)))
  exact (four.tail (step (.leaveValues updated result))).tail (step (.leaveFrame updated _ rfl))

private theorem trappedArm {A : Type} (selector : BitVec 32) (tail : List A) :
    Runs (.armTrap (args 0 selector) [i32 22] tail) (.caller (args 0 selector) true) := by
  have cut : Prefix.Discard [i32 22] tail [] [] := by
    simpa only [List.nil_append, List.append_nil] using
      Prefix.Discard.cut [] [i32 22] tail [] (.inl (by simp))
  exact ((Relation.ReflTransGen.single (.discard cut)).tail
    (.leaveTrapArm _)).tail (.leaveLoop _ true)

private theorem callerTrap (selector : BitVec 32) :
    program.FrameRuns entry.address (entryPhase entry (args 0 selector) true) (.done .trap) := by
  have step {a b : Graph.Phase} := (program.frameEdge_iff (a := a) (b := b) (fn := owner) (address := ⟨2⟩) rfl).mpr
  have cut : Prefix.Discard [i64 42] entry.tail [] [] := by
    simpa only [List.nil_append, List.append_nil] using
      Prefix.Discard.cut [] [i64 42] entry.tail [] (.inl (by simp))
  have discarded := Relation.ReflTransGen.single (step (.discard (locals := args 0 selector) cut))
  exact (discarded.tail (step (.leaveTrap _))).tail (step (.leaveFrame _ .trap trivial))

private theorem coreFromEntry {selector : BitVec 32} {dst : Core.Config Unit}
    (after : Core.Steps spec noHost (entry.coreConfig coreStore outer ⟨args 0 selector, .site⟩) dst) :
    Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 1 selector)) dst :=
  (Loop.core_run_iff (P := spec) (checked selector) rfl coreLinks).mpr
    (.inr (.inr (.inr ⟨_, reachesSite selector, after⟩)))

private theorem coreSiteResolved (selector : BitVec 32) {call : Context.Invocation}
    (invoked : (active selector).invocation program = some call)
    (w : Writes entry call.saved call.site.signature.results) {dst : Core.Config Unit} :
    Core.Steps spec noHost (entry.coreConfig coreStore outer ⟨args 0 selector, .site⟩) dst ↔
      dst ∈ [([], entry.before), ([i32 22], [.get ⟨5⟩])].map (entry.coreOperands coreStore outer (args 0 selector)) ++
        ((Outcome.resolved call.address).coreTrace.map (entry.coreLookup coreStore outer (active selector))) ∨
      CalleeFinish program call (coreCallee entry coreStore outer call)
        (fun outcome => Finish entry program (corePhase entry coreStore outer)
          (Graph.coreConfig coreStore outer entry.cont.target)
          (delivery call.caller call.saved w.indices (entry.insideTail.map Graph.coreEmit) outcome)) dst :=
  core_resolved_run (P := spec) (checked selector) (operands selector) (prepared selector) rfl invoked
    coreTable (coreTargets selector) coreLinks w (dst := dst)

private theorem coreSiteNull {dst : Core.Config Unit} :
    Core.Steps spec noHost (entry.coreConfig coreStore outer ⟨args 0 1, .site⟩) dst ↔
      dst ∈ [([], entry.before), ([i32 22], [.get ⟨5⟩])].map (entry.coreOperands coreStore outer (args 0 1)) ++
        (Outcome.null.coreTrace.map (entry.coreLookup coreStore outer (active 1))).dropLast ∨
      Finish entry program (corePhase entry coreStore outer)
        (Graph.coreConfig coreStore outer entry.cont.target) (coreTrap entry (active 1) .null) dst :=
  core_lookup_trap_run (P := spec) (checked 1) (operands 1) (prepared 1) rfl rfl LookupTrap.null
    coreTable (coreTargets 1) coreLinks (dst := dst)

example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 1 0))
    ⟨coreStore, outer.toCore, coreValues result⟩ :=
  coreFromEntry ((coreSiteResolved 0 (call := success) rfl (writes 0)).mpr
    (.inr (.inr ⟨.values returned, calleeReturn,
      .inr ⟨updated, false, savedAndWritten _, _, callerReturn, rfl⟩⟩)))

example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 1 1))
    ⟨coreStore, outer.toCore, [.trap]⟩ :=
  coreFromEntry (coreSiteNull.mpr (.inr (.inr ⟨args 0 1, true, trappedArm 1 _, _, callerTrap 1, rfl⟩)))

example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 1 2))
    ⟨coreStore, outer.toCore, [.trap]⟩ :=
  coreFromEntry ((coreSiteResolved 2 (call := failing) rfl (writes 2)).mpr
    (.inr (.inr ⟨.trap, calleeTrap,
      .inr ⟨args 0 2, true, trappedArm 2 _, _, callerTrap 2, rfl⟩⟩)))

example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 1 1))
    (corePhase entry coreStore outer (.caller (args 0 1) true)) :=
  coreFromEntry (coreSiteNull.mpr (.inr (.inl ⟨_, trappedArm 1 _, rfl⟩)))

example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 1 2))
    (coreCallee entry coreStore outer failing (.exit [] .trap)) :=
  coreFromEntry ((coreSiteResolved 2 (call := failing) rfl (writes 2)).mpr
    (.inr (.inl ⟨_, calleeTrapUpToFrameExit, rfl⟩)))

private theorem limeFromEntry {selector : BitVec 32} {dst : Lime1.Execution.Config Unit}
    (after : Lime1.Execution.Steps CallFrame.limeNoHost (entry.limeConfig limeStore outer ⟨args 0 selector, .site⟩) dst) :
    Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 1 selector)) dst :=
  (Loop.lime_run_iff (checked selector) rfl limeLinks).mpr
    (.inr (.inr (.inr ⟨_, reachesSite selector, after⟩)))

private theorem limeSiteResolved (selector : BitVec 32) {call : Context.Invocation}
    (invoked : (active selector).invocation program = some call)
    (w : Writes entry call.saved call.site.signature.results) {dst : Lime1.Execution.Config Unit} :
    Lime1.Execution.Steps CallFrame.limeNoHost (entry.limeConfig limeStore outer ⟨args 0 selector, .site⟩) dst ↔
      dst ∈ [([], entry.before), ([i32 22], [.get ⟨5⟩])].map (entry.limeOperands limeStore outer (args 0 selector)) ++
        [entry.limeLookup limeStore outer (active selector),
        entry.limeLookupResult limeStore outer (active selector) (.resolved call.address)] ∨
      CalleeFinish program call (limeCallee entry limeStore outer call)
        (fun outcome => Finish entry program (limePhase entry limeStore outer)
          (Graph.limeConfig limeStore outer entry.cont.target)
          (delivery call.caller call.saved w.indices (entry.insideTail.map Graph.limeEmit) outcome)) dst :=
  lime_resolved_run (checked selector) (operands selector) (prepared selector) rfl invoked
    limeTable (limeTargets selector) limeLinks w (dst := dst)

private theorem limeSiteNull {dst : Lime1.Execution.Config Unit} :
    Lime1.Execution.Steps CallFrame.limeNoHost (entry.limeConfig limeStore outer ⟨args 0 1, .site⟩) dst ↔
      dst ∈ [([], entry.before), ([i32 22], [.get ⟨5⟩])].map (entry.limeOperands limeStore outer (args 0 1)) ++
        [entry.limeLookup limeStore outer (active 1)] ∨
      Finish entry program (limePhase entry limeStore outer)
        (Graph.limeConfig limeStore outer entry.cont.target) (limeTrap entry (active 1)) dst :=
  lime_lookup_trap_run (checked 1) (operands 1) (prepared 1) rfl rfl LookupTrap.null
    limeTable (limeTargets 1) limeLinks (dst := dst)

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 1 0))
    ⟨limeStore, outer, Lime1.Execution.values result⟩ :=
  limeFromEntry ((limeSiteResolved 0 (call := success) rfl (writes 0)).mpr
    (.inr (.inr ⟨.values returned, calleeReturn,
      .inr ⟨updated, false, savedAndWritten _, _, callerReturn, rfl⟩⟩)))

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 1 1))
    ⟨limeStore, outer, [.trap]⟩ :=
  limeFromEntry (limeSiteNull.mpr (.inr (.inr ⟨args 0 1, true, trappedArm 1 _, _, callerTrap 1, rfl⟩)))

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 1 2))
    ⟨limeStore, outer, [.trap]⟩ :=
  limeFromEntry ((limeSiteResolved 2 (call := failing) rfl (writes 2)).mpr
    (.inr (.inr ⟨.trap, calleeTrap,
      .inr ⟨args 0 2, true, trappedArm 2 _, _, callerTrap 2, rfl⟩⟩)))

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 1 1))
    (limePhase entry limeStore outer (.caller (args 0 1) true)) :=
  limeFromEntry (limeSiteNull.mpr (.inr (.inl ⟨_, trappedArm 1 _, rfl⟩)))

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 1 2))
    (limeCallee entry limeStore outer failing (.exit [] .trap)) :=
  limeFromEntry ((limeSiteResolved 2 (call := failing) rfl (writes 2)).mpr
    (.inr (.inl ⟨_, calleeTrapUpToFrameExit, rfl⟩)))
