import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame Value)
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

private def signature : V1.FuncType := ⟨[], []⟩
private def ownerType : V1.FuncType :=
  ⟨[.int .i32, .int .i32, .int .i32], [.int .i64, .int .i32]⟩
private def owner : Graph.Function :=
  ⟨⟨{ types := [ownerType, signature], tables := [⟨0⟩] }, ⟨0⟩, ownerType.params, [], ownerType.results⟩,
    0, [i64 42], [.unreachable]⟩
private def program : Graph.Program := ⟨[some owner]⟩
private def tables : Source.Tables := [⟨[none], some 1⟩]
private def outer : Frame := ⟨[i32 77], { funcs := [⟨0⟩] }⟩
private def args (restart next choose : BitVec 32) : List Value := [i32 restart, i32 next, i32 choose]
private def entry : Loop.Entry :=
  { address := ⟨0⟩, owner, result := none, restart := ⟨0⟩, nextRestart := ⟨1⟩,
    branchTypes := [], choose := ⟨2⟩, op := ⟨⟨1⟩, signature⟩, before := [.get ⟨0⟩],
    insideTail := [], tail := [.numeric (.get ⟨0⟩)] }

private theorem checked (r n c : BitVec 32) : entry.Checked program tables outer ⟨0⟩ (args r n c) :=
  ⟨rfl, rfl, rfl, rfl⟩

example : { entry with branchTypes := [.int .i32] }.check program tables = false := rfl
example : { entry with result := some (.int .i32) }.check program tables = false := rfl
example : { entry with choose := ⟨3⟩ }.check program tables = false := rfl

private theorem trip (r n c : BitVec 32) :
    Loop.Runs entry ⟨args r n c, .enter⟩
      ⟨args n n c, if r = 0 then .readChoice else .branch⟩ := by
  have write := Locals.fact (.set (args r n c) entry.restart (i32 n) (by change 0 < 3; decide))
  have read : Loop.Runs entry ⟨args r n c, .enter⟩ ⟨args r n c, .writeRestart r n⟩ :=
    ((Relation.ReflTransGen.single Loop.Edge.enter).tail (.readRestart rfl)).tail (.readNext rfl)
  exact (read.tail (.writeRestart write)).tail .testRestart

private theorem restarted (c : BitVec 32) :
    Loop.Runs entry (entry.initial (args 1 0 c)) ⟨args 0 0 c, .enter⟩ :=
  (trip 1 0 c).tail .restart

private theorem reachesSite :
    Loop.Runs entry (entry.initial (args 1 0 1)) ⟨args 0 0 1, .site⟩ :=
  (((restarted 1).trans (trip 0 0 1)).tail (.readChoice rfl) |>.tail .testChoice).tail .enterSite

private theorem reachesTail :
    Loop.Runs entry (entry.initial (args 1 0 0)) ⟨args 0 0 0, .caller⟩ := by
  have read := ((restarted 0).trans (trip 0 0 0)).tail (.readChoice rfl)
  exact (((read.tail .testChoice).tail .enterEmpty).tail .leaveEmpty).tail .leaveLoop

private def coreStore : Core.Store Unit := { funcs := [entry.coreInstance] }
private def limeStore : Lime1.Execution.Store Unit := { funcs := [entry.limeInstance] }

private theorem noTargets (address : Runtime.FuncAddr) (fn : Graph.Function)
    (found : program.lookup address = some fn) : fn.targets = [] := by
  rcases address with ⟨_ | n⟩
  · obtain rfl := Option.some.inj found.symm
    rfl
  · cases found

private theorem coreLinks : program.CoreLinksAllocated coreStore :=
  fun a fn found _ used => (List.not_mem_nil (noTargets a fn found ▸ used)).elim

private theorem limeLinks : program.LimeLinksAllocated limeStore :=
  fun a fn found _ used => (List.not_mem_nil (noTargets a fn found ▸ used)).elim

-- The native endpoint is the reinstated source loop with the old flag replaced.
example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 1 0 1))
    (entry.coreConfig coreStore outer ⟨args 0 0 1, .enter⟩) :=
  (Loop.core_run_iff (P := spec) (checked 1 0 1) rfl coreLinks).mpr
    (.inr (.inl ⟨_, restarted 1, rfl⟩))

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 1 0 1))
    (entry.limeConfig limeStore outer ⟨args 0 0 1, .site⟩) :=
  (Loop.lime_run_iff (checked 1 0 1) rfl limeLinks).mpr (.inr (.inl ⟨_, reachesSite, rfl⟩))

private def out : List Value := [i64 42, i32 0]

private theorem tailDone : program.FrameRuns ⟨0⟩ (entry.callerPhase (args 0 0 0)) (.done (.values out)) := by
  have edge {a b : Graph.Phase} :=
    (program.frameEdge_iff (a := a) (b := b) (fn := owner) (address := ⟨0⟩) rfl).mpr
  have get := Relation.ReflTransGen.single (edge (.numeric (locals := args 0 0 0) (rest := [])
    (.get (stack := [i64 42]) (i := ⟨0⟩) (v := i32 0) rfl)))
  exact (get.tail (edge (.leaveValues (args 0 0 0) out))).tail
    (edge (.leaveFrame (args 0 0 0) (.values out) rfl))

-- Without a native table the empty arm still restores the original saved
-- i64, reads the updated local, and exits into the unchanged calling frame.
example : coreStore.tables = [] := rfl
example : limeStore.tables = [] := rfl

example : Core.Steps spec noHost (coreSource coreStore outer ⟨0⟩ (args 1 0 0))
    ⟨coreStore, outer.toCore, coreValues out⟩ :=
  (Loop.core_run_iff (P := spec) (checked 1 0 0) rfl coreLinks).mpr
    (.inr (.inr (.inl ⟨_, reachesTail, _, tailDone, .done rfl, rfl⟩)))

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore outer ⟨0⟩ (args 1 0 0))
    ⟨limeStore, outer, Lime1.Execution.values out⟩ :=
  (Loop.lime_run_iff (checked 1 0 0) rfl limeLinks).mpr
    (.inr (.inr (.inl ⟨_, reachesTail, _, tailDone, .done rfl, rfl⟩)))

private def coreWithTable : Core.Store Unit :=
  { coreStore with tables := tables.map Runtime.TableInst.toCore }
private def limeWithTable : Lime1.Execution.Store Unit := { limeStore with tables }
private def active : Source.Activation :=
  ⟨entry.frame (args 0 0 1), ⟨⟨0⟩, ⟨⟨[none], some 1⟩, ⟨1⟩, signature⟩⟩, ⟨[], [], 0⟩⟩

private theorem prepared :
    entry.op.prepare program tables (entry.frame (args 0 0 1)) [i32 0] = some active := rfl
private theorem checkedActive : active.Checked program tables := (Source.prepare_spec prepared).checked
private theorem operands :
    OperandTrace (args 0 0 1) [] entry.before [([], entry.before)] (.values [i32 0]) :=
  .value (.get rfl) (.done _)

private theorem coreTable : Source.Tables.CoreAllocated tables coreWithTable := by
  intro address table found
  simp [coreWithTable, List.getElem?_map, found]

private theorem limeTable : Source.Tables.LimeAllocated tables limeWithTable :=
  fun _ _ found => found

private theorem coreTargets : active.binding.site.CoreAllocated program coreWithTable := by
  intro address _ used
  have impossible : some address ∈ ([none] : List (Option Runtime.FuncAddr)) := used
  simp at impossible

private theorem limeTargets : active.binding.site.LimeAllocated program limeWithTable := by
  intro address _ used
  have impossible : some address ∈ ([none] : List (Option Runtime.FuncAddr)) := used
  simp at impossible

-- The selector reads the updated restart local. Zero hits the null slot,
-- whereas the original flag would have selected an out-of-bounds index.
example : active.resolve program = some .null := rfl
example : { active with operands := ⟨[], [], 1⟩ }.resolve program = some .bounds := rfl

example : Core.Steps spec noHost (coreSource coreWithTable outer ⟨0⟩ (args 1 0 1))
    (entry.coreLookup coreWithTable outer active .nullTrap) := by
  have chain := Loop.core_lookup_exact (entry := entry) (outerFrame := outer) (P := spec)
    checkedActive coreTargets coreTable (out := .null) rfl
  have lookup : Core.Steps spec noHost (entry.coreLookup coreWithTable outer active .start)
      (entry.coreLookup coreWithTable outer active .nullTrap) :=
    (Context.Resume.prefix_run_iff
      ([.start, .lookup, .cast none, .call none].map (entry.coreLookup coreWithTable outer active))
      (entry.coreLookup coreWithTable outer active .nullTrap) chain).mpr (.inr .refl)
  have prefixRun := (Loop.core_operand_run_iff (entry := entry) (s := coreWithTable)
    (outerFrame := outer) (P := spec) operands).mpr
    (.inr ((Loop.core_lookup_start (entry := entry) (s := coreWithTable) (outerFrame := outer) prepared).symm ▸ lookup))
  apply (Loop.core_run_iff (P := spec) (checked 1 0 1) rfl ?_).mpr
    (.inr (.inr (.inr ⟨_, reachesSite, prefixRun⟩)))
  exact fun a fn found _ used => (List.not_mem_nil (noTargets a fn found ▸ used)).elim

example : Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeWithTable outer ⟨0⟩ (args 1 0 1))
    (entry.limeLookupResult limeWithTable outer active .null) := by
  have lookup := (Loop.lime_lookup_exact (entry := entry) (outerFrame := outer)
    checkedActive limeTargets limeTable (out := .null) rfl _).mpr rfl
  have after := Relation.ReflTransGen.single lookup
  have prefixRun := (Loop.lime_operand_run_iff (entry := entry) (s := limeWithTable)
    (outerFrame := outer) operands).mpr
    (.inr ((Loop.lime_lookup_start (entry := entry) (s := limeWithTable) (outerFrame := outer) prepared).symm ▸ after))
  apply (Loop.lime_run_iff (checked 1 0 1) rfl ?_).mpr (.inr (.inr (.inr ⟨_, reachesSite, prefixRun⟩)))
  exact fun a fn found _ used => (List.not_mem_nil (noTargets a fn found ▸ used)).elim
