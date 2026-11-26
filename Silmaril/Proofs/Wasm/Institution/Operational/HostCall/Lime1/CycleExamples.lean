module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.CycleExamples

open Execution.Runtime (Frame FuncAddr FuncInst ModuleInst Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall (CallTarget Declaration)
open CallContinuation.OuterCall.Ranked
open IndexedLoop (Edge Program State call_run_iff producerType)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64

private def empty : ByteArray := ⟨#[0, 0, 0, 0, 0, 0]⟩
private def written : ByteArray := ⟨#[0, 1, 2, 3, 4, 0]⟩
private abbrev word : BitVec 32 := 0x04030201
private def signature : Wasm.Lime1.FuncType := ⟨[.int .i32], [.int .i32]⟩
private def moduleAt : ModuleInst :=
  { types := [signature], funcs := [⟨1⟩], tables := [⟨0⟩], memories := [⟨0⟩] }
private def declaration : Declaration := ⟨moduleAt, ⟨0⟩, signature.params, [], signature.results⟩
private def callB : CallTarget := ⟨⟨0⟩, ⟨1⟩, declaration⟩
private def getSelector : Graph.Memory32.Op := .ranked (.numeric (.get ⟨0⟩))
private def choose : Graph.Memory32.Op := .callIndirect ⟨0⟩ ⟨signature.params, signature.results⟩

-- A writes before calling B. B uses the live selector to call A again or
-- to choose a returning leaf. All three functions have the same signature.
private def aFn : Graph.Memory32.Function :=
  ⟨declaration, 0, [i32 0, i32 word], [.store 1, getSelector, .ranked (.call callB)]⟩
private def bFn : Graph.Memory32.Function :=
  ⟨declaration, 0, [], [getSelector, getSelector, choose]⟩
private def leafFn : Graph.Memory32.Function := ⟨declaration, 0, [i32 42], []⟩

private def a : MemoryTarget := ⟨⟨0⟩, aFn⟩
private def b : MemoryTarget := ⟨⟨1⟩, bFn⟩
private def leaf : MemoryTarget := ⟨⟨2⟩, leafFn⟩
private def table : Execution.Runtime.TableInst := ⟨[some a.address, some leaf.address], none⟩

private def site : IndirectSite where
  toSite := ⟨table, ⟨1⟩, signature⟩
  graph := ⟨[]⟩
  memoryFunctions := [some aFn, some bFn, some leafFn]
  memoryCalls := .recursive

private def prepare : Site Nat :=
  ⟨⟨5⟩, ⟨[.int .i64, .int .i32], [.int .i64, .int .i32, .int .i32]⟩, 1⟩
private def saved : List Value := [i64 77]
private def dispatch : List (Continuation.Op Nat) := [.callIndirect site]

private def program : Program Nat where
  module := {
    types := [IndexedLoop.signature, signature, ⟨[.int .i64], [.int .i64, .int .i32]⟩]
    funcs := [⟨4⟩, ⟨5⟩]
    tables := [⟨0⟩]
    memories := [⟨0⟩] }
  rootAddress := ⟨3⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨4⟩
  producerCode := 0
  continuation := .call ⟨1⟩ prepare :: dispatch
  saved := 99
  functionIndex := ⟨2⟩
  functionResults := [.int .i64, .int .i32]

private def caller : Frame := ⟨[], { funcs := [⟨3⟩] }⟩
private def base : Store Nat :=
  { memories := [⟨empty, some 1⟩], tables := [table], funcs :=
    [.wasm signature moduleAt a.code, .wasm signature moduleAt b.code, .wasm signature moduleAt leaf.code,
      .wasm program.functionType program.module program.function, .host producerType 0, .host prepare.type 1] }
private def mem : Memory32 base := ⟨⟨0⟩, ⟨empty, some 1⟩, rfl, .fixed⟩
private def host : HostSemantics Nat := fun code store operands outcome =>
  match code with
  | 0 => store = base ∧ operands = [i64 7] ∧
      outcome = .returned base (.values [i32 1, i64 88, i32 0])
  | 1 => store = base ∧ operands = [i64 99, i32 1] ∧ ∃ selector : BitVec 32,
      outcome = .returned base (.values (saved ++ [i32 selector, i32 0]))
  | _ => False

private theorem tableEntries {address : FuncAddr} (member : some address ∈ site.table.refs) :
    address = a.address ∨ address = leaf.address := by
  simpa [site, table] using member

private theorem registered {callee : MemoryTarget} (found : site.memoryLookup callee.address = some callee.fn) :
    callee = a ∨ callee = b ∨ callee = leaf := by
  rcases callee with ⟨⟨address⟩, fn⟩
  rcases address with _ | _ | _ | address <;> simp_all [IndirectSite.memoryLookup, site, a, b, leaf]

private theorem outerLinked : site.Linked base program.module := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro address fn found
    simp [site, Graph.Program.lookup] at found
  · intro address member
    rcases tableEntries member with rfl | rfl
    · exact ⟨.wasm signature moduleAt a.code, rfl, fun _ => .inr ⟨aFn, rfl, rfl⟩⟩
    · exact ⟨.wasm signature moduleAt leaf.code, rfl, fun _ => .inr ⟨leafFn, rfl, rfl⟩⟩

private theorem directLink : site.MemoryDirect (base := base) a callB b := ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem innerLinked : site.MemoryIndirect mem host b ⟨0⟩ ⟨signature.params, signature.results⟩ := by
  refine ⟨rfl, rfl, fun address member => ?_⟩
  rcases tableEntries member with rfl | rfl
  · exact ⟨.wasm signature moduleAt a.code, rfl, fun _ => ⟨aFn, rfl, rfl, trivial⟩⟩
  · exact ⟨.wasm signature moduleAt leaf.code, rfl, fun _ => ⟨leafFn, rfl, rfl, trivial⟩⟩

private theorem graphLinked : site.MemoryLinked mem host := by
  constructor
  · intro callee found
    rcases registered found with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · intro parent found target used
    rcases registered found with rfl | rfl | rfl
    · have same : target = callB := by
        simpa [a, aFn, getSelector, Graph.Memory32.Function.targets, Graph.Memory32.Op.targets,
          Graph.Op.targets] using used
      subst target
      exact .inl ⟨b, directLink, trivial⟩
    · simp [b, bFn, getSelector, choose, Graph.Memory32.Function.targets, Graph.Memory32.Op.targets,
        Graph.Op.targets] at used
    · simp [leaf, leafFn, Graph.Memory32.Function.targets] at used
  · intro parent found index ty used
    rcases registered found with rfl | rfl | rfl
    · simp [a, aFn, getSelector] at used
    · have same : Graph.Memory32.Op.callIndirect index ty = choose := by
        simpa [b, bFn, getSelector] using used
      change Graph.Memory32.Op.callIndirect index ty =
        .callIndirect ⟨0⟩ ⟨signature.params, signature.results⟩ at same
      obtain ⟨rfl, rfl⟩ := Graph.Memory32.Op.callIndirect.inj same
      exact innerLinked
    · simp [leaf, leafFn] at used

-- The same graph cannot supply the strict admission policy. A's direct site
-- is well linked but its allocated target has the same rank.
example : ¬ site.MemoryLinked mem host .ranked := by
  intro linked
  have used : callB ∈ a.fn.targets := by decide
  rcases linked.direct a rfl callB used with ⟨child, link, rank⟩ | ⟨code, link⟩
  · exact Nat.not_lt_zero _ rank
  · have eq := link.allocated
    change some (.wasm signature moduleAt b.code : FuncInst Wasm.Lime1.Func Nat) =
      some (.host signature code) at eq
    cases eq

private theorem programChecked : program.Checked mem caller ⟨0⟩ := by
  have suffix : Continuation.Checked base program.module [.int .i64] [[.int .i64, .int .i32]]
      [.int .i64, .int .i32] [.int .i64, .int .i32, .int .i32] dispatch :=
    .callIndirect (saved := [.int .i64]) outerLinked .nil
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    .call (site := prepare) (saved := []) rfl (show prepare.Allocated base from rfl) suffix, rfl, rfl⟩

private theorem programContract : program.Contract mem host := by
  have prepared : prepare.Contract mem host := by
    intro _ _ _ _ _ _ answer
    obtain ⟨_, _, _, eq⟩ := answer
    cases eq
    exact ⟨empty, rfl, rfl, rfl⟩
  have dispatchContract : site.Contract mem host := by
    refine ⟨?_, graphLinked⟩
    intro address code member allocated
    rcases tableEntries member with rfl | rfl
    · cases (show some (.wasm signature moduleAt a.code : FuncInst Wasm.Lime1.Func Nat) =
        some (.host signature code) from allocated)
    · cases (show some (.wasm signature moduleAt leaf.code : FuncInst Wasm.Lime1.Func Nat) =
        some (.host signature code) from allocated)
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨empty, rfl, rfl, rfl⟩
  · exact .call prepared (.callIndirect dispatchContract .nil)

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program mem host 7) ⟨empty, .source⟩
private abbrev BodyPath (bytes : ByteArray) (phase : Continuation.Phase Nat) :=
  Path ⟨bytes, .continuation phase []⟩

private theorem atInvoke (selector : BitVec 32) : BodyPath empty (.memory saved site a (.invoke [i32 selector]) []) := by
  have producer : Path ⟨empty, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have answered : Edge program mem host 7 ⟨empty, .producerInvoke 7⟩ ⟨empty, .test 1 88 0⟩ :=
    .producerReturns rfl ⟨rfl, rfl, rfl⟩
  have exit : BodyPath empty (.source [i64 99, i32 1] program.continuation) :=
    (((producer.tail answered).tail (.control (.test 1 88 0))).tail
      (.control (.dropInput 1 88))).tail (.control (.loopResult 1))
  have preparing : BodyPath empty (.invoke [] prepare [i64 99, i32 1] dispatch) :=
    exit.tail (.continuation (.resolve (saved := []) (args := [i64 99, i32 1]) rfl))
  have prepared : BodyPath empty (.source ((saved ++ [i32 selector]) ++ [i32 0]) dispatch) :=
    preparing.tail (.continuation (.returned (vs := saved ++ [i32 selector, i32 0]) rfl rfl
      ⟨rfl, rfl, selector, rfl⟩))
  exact prepared.tail (.continuation (.callIndirect (saved := saved) (args := [i32 selector]) rfl
    (.memory (callee := a) rfl rfl (show a.Allocated base from rfl) rfl)))

private abbrev Position := ByteArray × MemoryCallee.Phase Nat
private def calleeStep (src dst : Position) : Prop :=
  MemoryCallee.Edge mem host site a src.1 src.2 dst.1 dst.2
private abbrev CalleeRun := Relation.ReflTransGen calleeStep

private theorem CalleeRun.advance {src : Position} {bytes nextBytes : ByteArray} {p q : MemoryCallee.Phase Nat}
    (run : CalleeRun src (bytes, p)) (move : MemoryCallee.Edge mem host site a bytes p nextBytes q) :
    CalleeRun src (nextBytes, q) :=
  run.tail move

private def inRoot (q : Position) : State Nat :=
  ⟨q.1, .continuation (.afterMemory saved site a [] q.2) []⟩

private theorem rootStep {src dst : Position} (move : calleeStep src dst) :
    Edge program mem host 7 (inRoot src) (inRoot dst) := by
  rcases src with ⟨bytes, phase⟩
  cases phase <;> try exact .continuation (.memory move)
  case done => cases move

private theorem rootRun {src dst : Position} (start : Path (inRoot src)) (run : CalleeRun src dst) :
    Path (inRoot dst) := by
  induction run with
  | refl => exact start
  | tail _ move ih => exact ih.tail (rootStep move)

private def inB (selector : BitVec 32) (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  .child [i32 selector] [] b phase []

private theorem toChoice (selector : BitVec 32) {before : ByteArray}
    (write : MemoryWrite.EdgeAt before 1 (.store 0 word) (.written written)) :
    CalleeRun (before, .invoke [i32 selector])
      (written, inB selector (.body [i32 selector] [i32 selector, i32 selector] [choose])) := by
  have entered : CalleeRun (before, .invoke [i32 selector]) (before, .body [i32 selector] aFn.initial aFn.code) :=
    Relation.ReflTransGen.single (.enter (callee := a))
  have stored : CalleeRun (before, .invoke [i32 selector])
      (written, .body [i32 selector] [] [getSelector, .ranked (.call callB)]) :=
    entered.advance (.store (saved := []) write)
  have operand : CalleeRun (before, .invoke [i32 selector])
      (written, .body [i32 selector] [i32 selector] [.ranked (.call callB)]) :=
    stored.advance (.get (v := i32 selector) rfl)
  have invoked : CalleeRun (before, .invoke [i32 selector]) (written, inB selector (.invoke [i32 selector])) :=
    operand.advance (.call (saved := []) (operands := [i32 selector]) directLink rfl)
  have inside : CalleeRun (before, .invoke [i32 selector])
      (written, inB selector (.body [i32 selector] [] bFn.code)) :=
    invoked.advance (.child .enter)
  have first : CalleeRun (before, .invoke [i32 selector])
      (written, inB selector (.body [i32 selector] [i32 selector] [getSelector, choose])) :=
    inside.advance (.child (.get (v := i32 selector) rfl))
  exact first.advance (.child (.get (v := i32 selector) rfl))

private theorem firstWrite : MemoryWrite.EdgeAt empty 1 (.store 0 word) (.written written) :=
  MemoryWrite.fact_at (.write 0 word written (by decide))

private def inLeaf (phase : MemoryCallee.Phase Nat) : MemoryCallee.Phase Nat :=
  inB 1 (.child [i32 1] [] leaf phase [])

-- Selector 1 chooses the base case and resumes both suspended frames with
-- their original operands and the write made before the call.
example : Steps host launch ⟨mem.store written, caller, values [i64 77, i32 42]⟩ := by
  have invoked : CalleeRun (empty, .invoke [i32 1]) (written, inLeaf (.invoke [i32 1])) :=
    (toChoice 1 firstWrite).advance
      (.child (.callIndirect (saved := []) (operands := [i32 1]) (child := leaf) (.memory rfl rfl (show leaf.Allocated base from rfl) rfl) rfl))
  have entered : CalleeRun (empty, .invoke [i32 1]) (written, inLeaf (.body [i32 1] [i32 42] [])) :=
    invoked.advance (.child (.child .enter))
  have leafLabel : CalleeRun (empty, .invoke [i32 1]) (written, inLeaf (.exit [i32 1] (.values [i32 42]))) :=
    entered.advance (.child (.child .labelDone))
  have resumedB : CalleeRun (empty, .invoke [i32 1])
      (written, inB 1 (.body [i32 1] [i32 42] [])) :=
    leafLabel.advance (.child (.child .frameDone))
  have bLabel : CalleeRun (empty, .invoke [i32 1]) (written, inB 1 (.exit [i32 1] (.values [i32 42]))) :=
    resumedB.advance (.child .labelDone)
  have resumedA : CalleeRun (empty, .invoke [i32 1]) (written, .body [i32 1] [i32 42] []) :=
    bLabel.advance (.child .frameDone)
  have aLabel : CalleeRun (empty, .invoke [i32 1]) (written, .exit [i32 1] (.values [i32 42])) :=
    resumedA.advance .labelDone
  have restored : BodyPath written (.source [i64 77, i32 42] []) :=
    rootRun (src := (empty, .invoke [i32 1])) (atInvoke 1) (aLabel.advance .frameDone)
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, (restored.tail (.continuation .labelResult)).tail (.continuation .frameDone), rfl, rfl⟩

private def insideCycle (q : Position) : Position :=
  (q.1, MemoryCallee.afterChild [i32 0] [] b [] (MemoryCallee.afterChild [i32 0] [] a [] q.2))

private theorem cycleStep {src dst : Position} (move : calleeStep src dst) :
    calleeStep (insideCycle src) (insideCycle dst) := by
  rcases src with ⟨bytes, phase⟩
  rcases dst with ⟨nextBytes, next⟩
  cases phase <;> try exact .child (.child move)
  case done => cases move

private theorem underCycle {src dst : Position} (run : CalleeRun src dst) :
    CalleeRun (insideCycle src) (insideCycle dst) := by
  induction run with
  | refl => exact .refl
  | tail _ move ih => exact ih.tail (cycleStep move)

private theorem oneCycle {before : ByteArray}
    (write : MemoryWrite.EdgeAt before 1 (.store 0 word) (.written written)) :
    CalleeRun (before, .invoke [i32 0]) (insideCycle (written, .invoke [i32 0])) :=
  (toChoice 0 write).advance
    (.child (.callIndirect (saved := []) (operands := [i32 0]) (child := a) (.memory rfl rfl (show a.Allocated base from rfl) rfl) rfl))

private def pendingAgain : Nat → Position
  | 0 => (written, .invoke [i32 0])
  | n + 1 => insideCycle (pendingAgain n)

private theorem repeatCycle (n : Nat) : CalleeRun (written, .invoke [i32 0]) (pendingAgain n) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    exact (oneCycle (MemoryWrite.fact_at (.write 0 word written (by decide)))).trans (underCycle ih)

-- Selector 0 revisits A. For each finite depth, the exact native endpoint
-- has another pending A invocation, suspended A/B frames and the live write.
example (n : Nat) : Steps host launch (program.render mem caller ⟨0⟩ 7 (inRoot (pendingAgain (n + 1)))) := by
  have reached := rootRun (src := (empty, .invoke [i32 0])) (atInvoke 0) ((oneCycle firstWrite).trans (underCycle (repeatCycle n)))
  have bytes (k : Nat) : (pendingAgain k).1 = written := by
    induction k with
    | zero => rfl
    | succ k ih => exact ih
  exact (call_run_iff (arg := 7) programChecked programContract).mpr
    ⟨_, reached, by change mem.Live (pendingAgain (n + 1)).1; rw [bytes]; rfl, rfl⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.CycleExamples
