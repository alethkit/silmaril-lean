module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame Value FuncAddr)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Numerics (Profile intBinOp)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed

private abbrev i32 := Value.int .i32
private abbrev int32 := NumType.int .i32
private abbrev div := Prefix.Op.bin .i32 (.div .signed)
private def remainder : List Prefix.Op := [.get ⟨0⟩, .bin .i32 .add]
private def continuation : List Prefix.Op := [.get ⟨2⟩, div] ++ remainder

private def callee : CallFrame.Callee := ⟨{}, ⟨0⟩, [int32], [], some int32, .locals [.get ⟨0⟩]⟩
private def trappingCallee : CallFrame.Callee := { callee with program := .unreachable }
private def caller : Frame := ⟨[.int .i64 85], { funcs := [⟨0⟩] }⟩

private def site (argDiv contDiv : BitVec 32) (fn : CallFrame.Callee) : Site :=
  ⟨⟨⟨0⟩, ⟨0⟩, ⟨1⟩, [i32 42, i32 argDiv, i32 contDiv], { funcs := [⟨1⟩] },
    ⟨0⟩, [int32, int32, int32], [], ⟨0⟩, fn, [.get ⟨0⟩, .get ⟨1⟩, div]⟩,
    continuation, some int32⟩

private def store (call : Site) : V1.Execution.Store Unit :=
  { funcs := [.wasm call.type call.outerModule call.v1Func, .wasm call.inner.type call.inner.module call.inner.v1Func] }

private theorem calleeReadOnly : ReadOnly callee.program := by simp [ReadOnly, callee]

private theorem registered (d e : BitVec 32) (fn : CallFrame.Callee)
    (params : fn.params = [int32]) (result : fn.result = some int32) (body : fn.program.Typed fn) (readOnly : ReadOnly fn.program) :
    V1Guard (store (site d e fn)) caller (site d e fn) := by
  refine ⟨⟨⟨⟨rfl, ?_, body, ?_⟩, ?_, readOnly⟩, rfl⟩, rfl, ⟨rfl, rfl⟩⟩
  · change Prefix.WellTyped _ [] _ fn.params
    rw [params]
    rfl
  · change (⟨0⟩ : FuncAddr) ≠ ⟨1⟩
    decide
  · change Prefix.check _ (fn.result.toList ++ _) _ = _
    rw [result]
    rfl

private theorem argsLoaded (d e : BitVec 32) (fn : CallFrame.Callee) :
    Runs (site d e fn) .call (.args [i32 42, i32 d] [div]) := by
  have enter := (Relation.ReflTransGen.single (fact (site := site d e fn) .resolve)).tail (fact .enter)
  exact (enter.tail (fact (.evaluate (.get rfl)))).tail (fact (.evaluate (.get rfl)))

private theorem argumentComputed (e : BitVec 32) (fn : CallFrame.Callee) :
    Runs (site 6 e fn) .call (.inner (.call [] [i32 7])) := by
  have ok : intBinOp .i32 (.div .signed) 42 6 = .ok 7 := rfl
  exact (argsLoaded 6 e fn).tail (fact (.evaluate (.bin (stack := []) ok)))

private theorem entersInner (e : BitVec 32) (fn : CallFrame.Callee) (arity : fn.params.length = 1) :
    StraightLine.Runs (site 6 e fn).innerSite (.call [] [i32 7]) (.active (.label [] (fn.init [i32 7]) (.code fn.program))) := by
  have start := Relation.ReflTransGen.single (StraightLine.fact (site := (site 6 e fn).innerSite)
    (.resolve [] [i32 7]))
  exact start.tail (StraightLine.call (by trivial) (CallFrame.fact (.enter [] [i32 7] arity.symm)))

private theorem returnsInner (e : BitVec 32) :
    StraightLine.Runs (site 6 e callee).innerSite (.call [] [i32 7]) (.resume [i32 7] continuation) := by
  have entry := entersInner e callee rfl
  have read := entry.tail (StraightLine.call (by trivial)
    (CallFrame.reduce [] (Locals.fact (.get [i32 7] ⟨0⟩ (i32 7) rfl))))
  have label := read.tail (StraightLine.call (by trivial) (CallFrame.fact (.labelValues [] [i32 7] [i32 7])))
  exact label.tail (StraightLine.call (by trivial) (CallFrame.fact (.frameValues [] [i32 7] [i32 7] rfl)))

private theorem normalPath : Runs (site 6 7 callee) .call (.inner (.boundary (.done (.values [i32 43])))) := by
  have read := (returnsInner 7).tail (StraightLine.fact (.resume (.get rfl)))
  have quotient : intBinOp .i32 (.div .signed) 7 7 = .ok 1 := rfl
  have divide := read.tail (StraightLine.fact (.resume (.bin (stack := []) quotient)))
  have lhs := divide.tail (StraightLine.fact (.resume (.get rfl)))
  have add : intBinOp .i32 .add 1 42 = .ok 43 := rfl
  have finish := lhs.tail (StraightLine.fact (.resume (.bin (stack := []) add)))
  have pop := finish.tail (StraightLine.fact (.boundary (.labelValues [i32 43])))
  exact (argumentComputed 7 callee).trans (inner_runs_iff.mpr
    ⟨_, pop.tail (StraightLine.fact (.boundary (.frameValues [i32 43] rfl))), rfl⟩)

private theorem noMoreThanTrap (site : Site) :
    StraightLine.Runs site.innerSite (StraightLine.trapped [] []) (.boundary (.done .trap)) :=
  (Relation.ReflTransGen.single (StraightLine.fact (.boundary .labelTrap))).tail
    (StraightLine.fact (.boundary .frameTrap))

private theorem finishTrap (site : Site) (head : Prefix.Op) (tail : List Prefix.Op) :
    StraightLine.Runs site.innerSite (.trapped [] (head :: tail)) (.boundary (.done .trap)) := by
  have cut := StraightLine.fact (site := site.innerSite)
    (.discard (.cut [] [] (head :: tail) [] (.inr (by simp))))
  apply Relation.ReflTransGen.head _ (noMoreThanTrap site)
  simpa only [List.nil_append, List.append_nil] using cut

private theorem argumentRejects :
    Edge (site 0 7 callee) (.args [i32 42, i32 0] [div])
      (.argumentTrap [] ((site 0 7 callee).pending [])) :=
  fact (.evaluate (.trap (stack := []) (Numerics.intBinOp_div_zero .i32 .signed 42)))

private theorem argumentTrapPath : Runs (site 0 7 callee) .call (.inner (.boundary (.done .trap))) := by
  have failure := (argsLoaded 0 7 callee).tail argumentRejects
  have dropped := failure.tail (fact (.discard (.cut [] [] [Pending.call] (continuation.map Pending.op) (.inr (by simp)))))
  have cleared := dropped.tail (fact (.discard (.cut [] [] (continuation.map Pending.op) [] (.inr (by simp [continuation])))))
  exact cleared.trans (inner_runs_iff.mpr ⟨_, noMoreThanTrap _, rfl⟩)

private theorem calleeRaises :
    StraightLine.Runs (site 6 7 trappingCallee).innerSite (.call [] [i32 7])
      (StraightLine.attach (site 6 7 trappingCallee).innerSite (.trapped [])) := by
  have raised := (entersInner 7 trappingCallee rfl).tail
    (StraightLine.call (by trivial) (CallFrame.fact (.unreachable [] [i32 7])))
  have pop := raised.tail (StraightLine.call (by trivial) (CallFrame.fact (.labelTrap [] [i32 7])))
  exact pop.tail (StraightLine.call (by trivial) (CallFrame.fact (.frameTrap [] [i32 7])))

private theorem calleeTrapPath : Runs (site 6 7 trappingCallee) .call (.inner (.boundary (.done .trap))) :=
  (argumentComputed 7 trappingCallee).trans (inner_runs_iff.mpr
    ⟨_, calleeRaises.trans (finishTrap _ (.get ⟨2⟩) (div :: remainder)), rfl⟩)

private theorem continuationRejects :
    StraightLine.Edge (site 6 0 callee).innerSite (.resume [i32 7, i32 0] (div :: remainder)) (.trapped [] remainder) :=
  StraightLine.fact (.resume (.trap (stack := []) (Numerics.intBinOp_div_zero .i32 .signed 7)))

private theorem continuationTrapPath : Runs (site 6 0 callee) .call (.inner (.boundary (.done .trap))) := by
  have read := (returnsInner 0).tail (StraightLine.fact (.resume (.get rfl)))
  have trapped := read.tail continuationRejects
  exact (argumentComputed 0 callee).trans (inner_runs_iff.mpr
    ⟨_, trapped.trans (finishTrap _ (.get ⟨0⟩) [.bin .i32 .add]), rfl⟩)

example : V1.Execution.Steps CallFrame.v1NoHost (v1Config (store (site 6 7 callee)) caller (site 6 7 callee) .call)
    ⟨store (site 6 7 callee), caller, [.source (.intConst .i32 43)]⟩ :=
  (v1_run_iff (registered 6 7 callee rfl rfl rfl calleeReadOnly) (a := .call) trivial).mpr ⟨_, normalPath, rfl, rfl⟩

example : V1.Execution.Step CallFrame.v1NoHost
    (v1Config (store (site 0 7 callee)) caller (site 0 7 callee) (.args [i32 42, i32 0] [div]))
    ⟨store (site 0 7 callee), caller, [.frame 1 (site 0 7 callee).toSite.frame [.label 1 []
      [.trap, .source (.call ⟨0⟩), .source (.localGet ⟨2⟩), .source (.intBinOp .i32 (.div .signed)),
        .source (.localGet ⟨0⟩), .source (.intBinOp .i32 .add)]]]⟩ :=
  v1_sound (registered 0 7 callee rfl rfl rfl calleeReadOnly) argumentRejects

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (v1Config (store (site 0 7 callee)) caller (site 0 7 callee) .call).toLime
    ⟨(store (site 0 7 callee)).mapCode V1.Func.toLime, caller, [.trap]⟩ := by
  rw [v1_to_lime]
  exact (lime_run_iff (guard_to_lime (registered 0 7 callee rfl rfl rfl calleeReadOnly)) (a := .call) trivial).mpr
    ⟨_, argumentTrapPath, trivial, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (v1Config (store (site 6 7 trappingCallee)) caller (site 6 7 trappingCallee) .call).toLime
    ⟨(store (site 6 7 trappingCallee)).mapCode V1.Func.toLime, caller, [.trap]⟩ := by
  rw [v1_to_lime]
  exact (lime_run_iff (guard_to_lime (registered 6 7 trappingCallee rfl rfl trivial trivial)) (a := .call) trivial).mpr
    ⟨_, calleeTrapPath, trivial, rfl⟩

example {out : State}
    (path : Runs (site 6 7 trappingCallee)
      (.inner (StraightLine.attach (site 6 7 trappingCallee).innerSite (.trapped []))) out) :
    ∃ phase, out = .inner phase ∧ StraightLine.Unwinding phase := by
  obtain ⟨phase, remaining, eq⟩ := inner_runs_iff.mp path
  exact ⟨phase, eq, StraightLine.callee_trap_bypasses remaining⟩

example : Core.Steps Profile.spec noHost
    (v1Config (store (site 6 0 callee)) caller (site 6 0 callee) .call).toLime.toCore
    ⟨((store (site 6 0 callee)).mapCode V1.Func.toLime).toCore, caller.toCore, [.trap]⟩ := by
  have g := guard_to_lime (registered 6 0 callee rfl rfl rfl calleeReadOnly)
  rw [v1_to_lime, lime_to_core g]
  exact (core_run_iff (guard_to_core g) (a := .call) trivial).mpr ⟨_, continuationTrapPath, trivial, rfl⟩

example : Core.Step Profile.spec noHost
    (v1Config (store (site 6 0 callee)) caller (site 6 0 callee) (.inner (.resume [i32 7, i32 0] (div :: remainder)))).toLime.toCore
    ⟨((store (site 6 0 callee)).mapCode V1.Func.toLime).toCore, caller.toCore, [.frame 1 (site 6 0 callee).toSite.frame.toCore
      [.label 1 [] [.trap, .plain (.localGet ⟨0⟩), .plain (.intBinOp .i32 .add)]]]⟩ := by
  have g := guard_to_lime (registered 6 0 callee rfl rfl rfl calleeReadOnly)
  rw [v1_to_lime, lime_to_core g]
  exact core_sound (guard_to_core g) (delegate continuationRejects)

example {target : Core.Config Unit}
    (run : Core.Steps Profile.spec noHost
      (v1Config (store (site 6 0 callee)) caller (site 6 0 callee) .call).toLime.toCore target) :
    ∃ out, Runs (site 6 0 callee) .call out ∧
      target = (v1Config (store (site 6 0 callee)) caller (site 6 0 callee) out).toLime.toCore := by
  have g := guard_to_lime (registered 6 0 callee rfl rfl rfl calleeReadOnly)
  rw [v1_to_lime, lime_to_core g] at run
  obtain ⟨out, steps, _, eq⟩ := (core_run_iff (guard_to_core g) (a := .call) trivial).mp run
  exact ⟨out, steps, by rw [v1_to_lime, lime_to_core g, eq]⟩

example : ¬ ReadOnly (.locals [.set ⟨0⟩]) := by
  intro ready
  exact (ready ⟨0⟩).1 (by simp)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed
