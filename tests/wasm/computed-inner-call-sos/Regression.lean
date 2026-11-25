module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame Value FuncAddr)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed
open Silmaril.Wasm.Numerics (Profile IntTrap intBinOp)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private def fn : CallFrame.Callee :=
  ⟨{}, ⟨0⟩, [.int .i32], [], some (.int .i32), .locals [.get ⟨0⟩]⟩

private def caller : Frame := ⟨[.int .i64 85], { funcs := [⟨0⟩] }⟩

private def site (x y : BitVec 32) : Site :=
  ⟨⟨0⟩, ⟨0⟩, ⟨1⟩, [.int .i32 x, .int .i32 y], { funcs := [⟨1⟩] }, ⟨0⟩,
    [.int .i32, .int .i32], [], ⟨0⟩, fn, .i32, ⟨0⟩, ⟨1⟩, .div .signed, x, y⟩

private def zeroSite : Site :=
  { site 42 0 with args := [.int .i32 42], params := [.int .i32], locals := [.int .i32] }

private def store (call : Site) : V1.Execution.Store Unit :=
  { funcs := [.wasm call.type call.outerModule call.v1Func, .wasm fn.type fn.module fn.v1Func] }

private theorem registered (x y : BitVec 32) : V1Guard (store (site x y)) caller (site x y) :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, by change (⟨0⟩ : FuncAddr) ≠ ⟨1⟩; decide⟩, rfl, rfl⟩, rfl, rfl⟩

private theorem zeroGuard : V1Guard (store zeroSite) caller zeroSite :=
  ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, by change (⟨0⟩ : FuncAddr) ≠ ⟨1⟩; decide⟩, rfl, rfl⟩, rfl, rfl⟩

private theorem stem (call : Site) : Runs call .call .compute :=
  (((Relation.ReflTransGen.single (fact .resolve)).tail (fact .enter)).tail
    (fact .readLeft)).tail (fact .readRight)

private theorem returned :
    Runs (site 42 6) .call (.nested (.done (.values [.int .i32 7]))) := by
  let v := Value.int .i32 7
  have ok : intBinOp .i32 (.div .signed) 42 6 = .ok 7 := rfl
  have resolved := ((stem (site 42 6)).tail (fact (.compute ok))).tail (fact (.resolveInner 7))
  have entered := resolved.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call
    (by trivial) (CallFrame.fact (.enter [] [v] rfl)))))
  have read := entered.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call
    (by trivial) (CallFrame.reduce [] (Locals.fact (.get [v] ⟨0⟩ v rfl))))))
  have label := read.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call
    (by trivial) (CallFrame.fact (.labelValues [] [v] [v])))))
  have frame := label.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.call
    (by trivial) (CallFrame.fact (.frameValues [] [v] [v] rfl)))))
  have nop := frame.tail (delegate (CallContinuation.Nested.underLabel (CallContinuation.fact (.resume [v]))))
  exact (nop.tail (delegate (CallContinuation.Nested.fact (.labelValues [v])))).tail
    (delegate (CallContinuation.Nested.fact (.frameValues [v] rfl)))

private theorem earlyTrap {call : Site} {e : IntTrap}
    (err : intBinOp call.kind call.op call.left call.right = .error e) :
    Runs call .call (.nested (.done .trap)) :=
  ((((stem call).tail (fact (.trap err))).tail (fact .dropCallAndNop)).tail
    (delegate (CallContinuation.Nested.fact .labelTrap))).tail (delegate (CallContinuation.Nested.fact .frameTrap))

private theorem zeroErr : intBinOp zeroSite.kind zeroSite.op zeroSite.left zeroSite.right = .error .divideByZero :=
  Numerics.intBinOp_div_zero .i32 .signed 42

example : V1.Execution.Steps CallFrame.v1NoHost (v1Config (store (site 42 6)) caller (site 42 6) .call)
    ⟨store (site 42 6), caller, [.source (.intConst .i32 7)]⟩ :=
  (v1_run_iff (registered 42 6) (a := .call) trivial).mpr ⟨_, returned, trivial, rfl⟩

example : V1.Execution.Steps CallFrame.v1NoHost (v1Config (store zeroSite) caller zeroSite .call)
    ⟨store zeroSite, caller, [.trap]⟩ :=
  (v1_run_iff zeroGuard (a := .call) trivial).mpr ⟨_, earlyTrap zeroErr, trivial, rfl⟩

example : Lime1.Execution.Step CallFrame.limeNoHost
    (v1Config (store zeroSite) caller zeroSite .compute).toLime
    ⟨(store zeroSite).mapCode V1.Func.toLime, caller, [.frame 1 zeroSite.frame
      [.label 1 [] [.trap, .source (.call ⟨0⟩), .source .nop]]]⟩ := by
  rw [v1_to_lime]
  exact lime_sound (guard_to_lime zeroGuard) (fact (.trap zeroErr))

example : Core.Step Profile.spec noHost
    (v1Config (store zeroSite) caller zeroSite .argumentTrap).toLime.toCore
    ⟨((store zeroSite).mapCode V1.Func.toLime).toCore, caller.toCore, [.frame 1 zeroSite.frame.toCore
      [.label 1 [] [.trap, .plain .nop]]]⟩ := by
  have g := guard_to_lime zeroGuard
  rw [v1_to_lime, lime_to_core g]
  exact core_sound (guard_to_core g) (fact .dropCall)

example : Core.Steps Profile.spec noHost
    (v1Config (store (site 0x80000000 (-1))) caller (site 0x80000000 (-1)) .call).toLime.toCore
    ⟨((store (site 0x80000000 (-1))).mapCode V1.Func.toLime).toCore, caller.toCore, [.trap]⟩ := by
  have g := guard_to_lime (registered 0x80000000 (-1))
  rw [v1_to_lime, lime_to_core g]
  exact (core_run_iff (guard_to_core g) (a := .call) trivial).mpr
    ⟨_, earlyTrap (e := .overflow) rfl, trivial, rfl⟩

example {target : Core.Config Unit}
    (run : Core.Steps Profile.spec noHost (v1Config (store zeroSite) caller zeroSite .call).toLime.toCore target) :
    ∃ out, Runs zeroSite .call out ∧ target = (v1Config (store zeroSite) caller zeroSite out).toLime.toCore := by
  have g := guard_to_lime zeroGuard
  rw [v1_to_lime, lime_to_core g] at run
  obtain ⟨out, path, _, eq⟩ := (core_run_iff (guard_to_core g) (a := .call) trivial).mp run
  exact ⟨out, path, by rw [v1_to_lime, lime_to_core g, eq]⟩

example : ¬ Typed { zeroSite with rightIndex := ⟨2⟩ } := fun h => by
  have invalid := h.rightLookup
  change (none : Option Value) = some (.int .i32 0) at invalid
  cases invalid
