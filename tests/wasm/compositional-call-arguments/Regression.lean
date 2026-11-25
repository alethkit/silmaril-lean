module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame Value FuncAddr)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Numerics (Profile intBinOp)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence

private abbrev i32 := Value.int .i32

private def leftCode : List Prefix.Op := [.get ⟨0⟩, .get ⟨1⟩, .get ⟨2⟩, .bin .i32 .sub]
private def rightCode : List Prefix.Op := [.get ⟨3⟩, .bin .i32 (.div .signed), .get ⟨2⟩]

private def inner : CallFrame.Callee :=
  ⟨{}, ⟨0⟩, [.int .i32, .int .i32, .int .i32], [], some (.int .i32), .locals [.get ⟨1⟩]⟩

private def caller : Frame := ⟨[.int .i64 85], { funcs := [⟨0⟩] }⟩

private def site (divisor : BitVec 32) : Site :=
  ⟨⟨0⟩, ⟨0⟩, ⟨1⟩, [i32 91, i32 42, i32 6, i32 divisor], { funcs := [⟨1⟩] }, ⟨0⟩,
    [.int .i32, .int .i32, .int .i32, .int .i32], [], ⟨0⟩, inner, leftCode ++ rightCode⟩

private def store (divisor : BitVec 32) : V1.Execution.Store Unit :=
  let call := site divisor
  { funcs := [.wasm call.type call.outerModule call.v1Func, .wasm inner.type inner.module inner.v1Func] }

private theorem registered (d : BitVec 32) : V1Guard (store d) caller (site d) := by
  refine ⟨⟨⟨rfl, ?_, rfl, ?_⟩, rfl, rfl⟩, rfl, rfl⟩
  · show Prefix.check ((site d).frame.locals.map Value.type) [] (leftCode ++ rightCode) = _
    rw [Prefix.check_append]
    rfl
  · change (⟨0⟩ : FuncAddr) ≠ ⟨1⟩
    decide

private theorem readyToDivide (d : BitVec 32) :
    Runs (site d) .call (.args [i32 91, i32 36, i32 d] [.bin .i32 (.div .signed), .get ⟨2⟩]) := by
  have entered := (Relation.ReflTransGen.single (fact (site := site d) .resolve)).tail (fact .enter)
  have first := entered.tail (fact (.arg (.get rfl)))
  have second := first.tail (fact (.arg (.get rfl)))
  have third := second.tail (fact (.arg (.get rfl)))
  have subtract : intBinOp .i32 .sub 42 6 = .ok 36 := rfl
  have difference := third.tail (fact (.arg (.bin (stack := [i32 91]) subtract)))
  exact difference.tail (fact (.arg (.get rfl)))

private def computedArgs : List Value := [i32 91, i32 12, i32 6]

private theorem resolves : Runs (site 3) .call (.nested (innerStart computedArgs)) := by
  have divide : intBinOp .i32 (.div .signed) 36 3 = .ok 12 := rfl
  have quotient := (readyToDivide 3).tail (fact (.arg (.bin (stack := [i32 91]) divide)))
  have all := quotient.tail (fact (.arg (.get rfl)))
  exact all.tail (fact (.resolveInner computedArgs))

private theorem returns : Runs (site 3) .call (.nested (.done (.values [i32 12]))) := by
  have enters := resolves.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call
    (by trivial) (CallFrame.fact (.enter [] computedArgs rfl)))))
  have read := enters.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call
    (by trivial) (CallFrame.reduce [] (Locals.fact (.get computedArgs ⟨1⟩ (i32 12) rfl))))))
  have label := read.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call
    (by trivial) (CallFrame.fact (.labelValues [] computedArgs [i32 12])))))
  have frame := label.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call
    (by trivial) (CallFrame.fact (.frameValues [] computedArgs [i32 12] rfl)))))
  have nop := frame.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.fact (.resume [i32 12]))))
  exact (nop.tail (delegate (CallContinuation.Nested.fact (.labelValues [i32 12])))).tail
    (delegate (CallContinuation.Nested.fact (.frameValues [i32 12] rfl)))

private theorem divideTraps :
    Edge (site 0) (.args [i32 91, i32 36, i32 0] [.bin .i32 (.div .signed), .get ⟨2⟩])
      (.trap [i32 91] (pending [.get ⟨2⟩])) :=
  fact (.trap (.trap (stack := [i32 91]) (Numerics.intBinOp_div_zero .i32 .signed 36)))

private theorem partialDiscard :
    Edge (site 0) (.trap [i32 91] (pending [.get ⟨2⟩])) (.trap [i32 91] [.call, .nop]) :=
  fact (.discard (.cut [i32 91] [] [.arg (.get ⟨2⟩)] [.call, .nop] (.inr (by simp))))

private theorem traps : Runs (site 0) .call (.nested (.done .trap)) := by
  have raised := (readyToDivide 0).tail divideTraps
  have trimmed := raised.tail partialDiscard
  have isolated := trimmed.tail (fact (.discard (.cut [] [i32 91] [Pending.call, Pending.nop] [] (.inl (by simp)))))
  exact (isolated.tail (delegate (CallContinuation.Nested.fact .labelTrap))).tail
    (delegate (CallContinuation.Nested.fact .frameTrap))

example : V1.Execution.Steps CallFrame.v1NoHost (v1Config (store 3) caller (site 3) .call)
    ⟨store 3, caller, [.source (.intConst .i32 12)]⟩ :=
  (v1_run_iff (registered 3) (a := .call) trivial).mpr ⟨_, returns, trivial, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost (v1Config (store 3) caller (site 3) .call).toLime
    ⟨(store 3).mapCode V1.Func.toLime, caller, [.frame 1 (site 3).frame [.label 1 []
      [.source (.intConst .i32 91), .source (.intConst .i32 12), .source (.intConst .i32 6),
        .invoke ⟨1⟩, .source .nop]]]⟩ := by
  rw [v1_to_lime]
  exact (lime_run_iff (guard_to_lime (registered 3)) (a := .call) trivial).mpr
    ⟨_, resolves, ⟨trivial, rfl, rfl⟩, rfl⟩

example : V1.Execution.Step CallFrame.v1NoHost
    (v1Config (store 0) caller (site 0) (.args [i32 91, i32 36, i32 0] [.bin .i32 (.div .signed), .get ⟨2⟩]))
    ⟨store 0, caller, [.frame 1 (site 0).frame [.label 1 []
      [.source (.intConst .i32 91), .trap, .source (.localGet ⟨2⟩), .source (.call ⟨0⟩), .source .nop]]]⟩ :=
  v1_sound (registered 0) divideTraps

example : Core.Step Profile.spec noHost
    (v1Config (store 0) caller (site 0) (.trap [i32 91] (pending [.get ⟨2⟩]))).toLime.toCore
    ⟨((store 0).mapCode V1.Func.toLime).toCore, caller.toCore, [.frame 1 (site 0).frame.toCore [.label 1 []
      [.plain (.intConst .i32 91), .trap, .plain (.call ⟨0⟩), .plain .nop]]]⟩ := by
  have g := guard_to_lime (registered 0)
  rw [v1_to_lime, lime_to_core g]
  exact core_sound (guard_to_core g) partialDiscard

example : Core.Steps Profile.spec noHost (v1Config (store 0) caller (site 0) .call).toLime.toCore
    ⟨((store 0).mapCode V1.Func.toLime).toCore, caller.toCore, [.trap]⟩ := by
  have g := guard_to_lime (registered 0)
  rw [v1_to_lime, lime_to_core g]
  exact (core_run_iff (guard_to_core g) (a := .call) trivial).mpr ⟨_, traps, trivial, rfl⟩

example {dst : Core.Config Unit}
    (path : Core.Steps Profile.spec noHost (v1Config (store 0) caller (site 0) .call).toLime.toCore dst) :
    ∃ out, Runs (site 0) .call out ∧ dst = (v1Config (store 0) caller (site 0) out).toLime.toCore := by
  have g := guard_to_lime (registered 0)
  rw [v1_to_lime, lime_to_core g] at path
  obtain ⟨out, run, _, eq⟩ := (core_run_iff (guard_to_core g) (a := .call) trivial).mp path
  exact ⟨out, run, by rw [v1_to_lime, lime_to_core g, eq]⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence
