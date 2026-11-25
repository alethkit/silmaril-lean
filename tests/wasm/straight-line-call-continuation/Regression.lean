module

import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame Value)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Numerics (Profile intBinOp)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine

open OuterCall.Computed

private abbrev i32 := Value.int .i32

private def saved : List Value := [i32 42]
private def outer : Frame := ⟨[i32 3], { funcs := [⟨0⟩] }⟩
private def caller : Frame := ⟨[.int .i64 85], {}⟩

private def returns : CallFrame.Callee :=
  ⟨{}, ⟨0⟩, [], [], some (.int .i32), .ret [i32 7]⟩

private def traps : CallFrame.Callee := { returns with program := .unreachable }

private def site (fn : CallFrame.Callee) : Site :=
  ⟨outer, ⟨0⟩, ⟨0⟩, fn, [.get ⟨0⟩, .bin .i32 .mul, .bin .i32 .add], some (.int .i32)⟩

private def store (fn : CallFrame.Callee) : V1.Execution.Store Unit :=
  { funcs := [.wasm fn.type fn.module fn.v1Func] }

private theorem registered (fn : CallFrame.Callee) : V1Guard (store fn) (site fn) := ⟨rfl, rfl⟩

private theorem returnSource : Admitted (site returns) (.call saved []) := ⟨⟨rfl, rfl⟩, rfl⟩
private theorem trapSource : Admitted (site traps) (.call saved []) := ⟨⟨rfl, trivial⟩, rfl⟩

private theorem enters (fn : CallFrame.Callee) (arity : fn.params.length = 0) :
    Runs (site fn) (.call saved []) (.active (.label saved (fn.init []) (.code fn.program))) :=
  (Relation.ReflTransGen.single (fact (.resolve saved []))).tail (call (by trivial) (CallFrame.fact (.enter saved [] arity.symm)))

private theorem reachesContinuation :
    Runs (site returns) (.call saved []) (.resume [i32 42, i32 7] (site returns).continuation) := by
  have label := (enters returns rfl).tail (call (by trivial) (CallFrame.fact (.labelReturn saved [] [i32 7])))
  exact label.tail (call (by trivial) (CallFrame.fact (.frameReturn saved [] [] [i32 7] rfl)))

private theorem returnPath :
    Runs (site returns) (.call saved []) (.boundary (.done (.values [i32 63]))) := by
  have read := reachesContinuation.tail (fact (.resume (.get rfl)))
  have mul : intBinOp .i32 .mul 7 3 = .ok 21 := rfl
  have product := read.tail (fact (.resume (.bin (stack := [i32 42]) mul)))
  have add : intBinOp .i32 .add 42 21 = .ok 63 := rfl
  have sum := product.tail (fact (.resume (.bin (stack := []) add)))
  exact (sum.tail (fact (.boundary (.labelValues [i32 63])))).tail
    (fact (.boundary (.frameValues [i32 63] rfl)))

private theorem raisesTrap :
    Runs (site traps) (.call saved []) (attach (site traps) (.trapped saved)) := by
  have one := (enters traps rfl).tail (call (by trivial) (CallFrame.fact (.unreachable saved [])))
  have two := one.tail (call (by trivial) (CallFrame.fact (.labelTrap saved [])))
  exact two.tail (call (by trivial) (CallFrame.fact (.frameTrap saved [])))

private def pending : List Prefix.Op := [.bin .i32 .mul, .bin .i32 .add]
private theorem cutsLocalRead : Edge (site traps) (attach (site traps) (.trapped saved)) (.trapped saved pending) :=
  fact (.discard (.cut saved [] [.get ⟨0⟩] pending (.inr (by simp))))

private theorem trapPath : Runs (site traps) (.call saved []) (.boundary (.done .trap)) := by
  have cut := raisesTrap.tail cutsLocalRead
  have isolated := cut.tail (fact (.discard (.cut [] saved pending [] (.inl (by simp [saved])))))
  exact (isolated.tail (fact (.boundary .labelTrap))).tail (fact (.boundary .frameTrap))

example : V1.Execution.Steps CallFrame.v1NoHost (v1Config (store returns) caller (site returns) (.call saved []))
    ⟨store returns, caller, [.source (.intConst .i32 63)]⟩ :=
  (v1_run_iff (registered returns) returnSource).mpr ⟨_, returnPath, rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost (v1Config (store returns) caller (site returns) (.call saved [])).toLime
    ⟨(store returns).mapCode V1.Func.toLime, caller, [.frame 1 outer [.label 1 []
      [.source (.intConst .i32 42), .source (.intConst .i32 7), .source (.localGet ⟨0⟩),
        .source (.intBinOp .i32 .mul), .source (.intBinOp .i32 .add)]]]⟩ := by
  rw [v1_to_lime]
  exact (lime_run_iff (guard_to_lime (registered returns)) returnSource).mpr
    ⟨_, reachesContinuation, ⟨by simp [site], rfl⟩, rfl⟩

example : Core.Step Profile.spec noHost
    (v1Config (store traps) caller (site traps) (attach (site traps) (.trapped saved))).toLime.toCore
    ⟨((store traps).mapCode V1.Func.toLime).toCore, caller.toCore, [.frame 1 outer.toCore [.label 1 []
      [.plain (.intConst .i32 42), .trap, .plain (.intBinOp .i32 .mul), .plain (.intBinOp .i32 .add)]]]⟩ := by
  have g := guard_to_lime (registered traps)
  rw [v1_to_lime, lime_to_core g]
  exact core_sound (guard_to_core g) cutsLocalRead

example : Core.Steps Profile.spec noHost (v1Config (store traps) caller (site traps) (.call saved [])).toLime.toCore
    ⟨((store traps).mapCode V1.Func.toLime).toCore, caller.toCore, [.trap]⟩ := by
  have g := guard_to_lime (registered traps)
  rw [v1_to_lime, lime_to_core g]
  exact (core_run_iff (guard_to_core g) trapSource).mpr ⟨_, trapPath, trivial, rfl⟩

example {target : Core.Config Unit}
    (run : Core.Steps Profile.spec noHost
      (v1Config (store traps) caller (site traps) (attach (site traps) (.trapped saved))).toLime.toCore target) :
    ∃ out, Unwinding out ∧ target = (v1Config (store traps) caller (site traps) out).toLime.toCore := by
  have g := guard_to_lime (registered traps)
  rw [v1_to_lime, lime_to_core g] at run
  have ready : Admitted (site traps) (attach (site traps) (.trapped saved)) := .inl (by simp [saved])
  obtain ⟨out, path, _, eq⟩ := (core_run_iff (guard_to_core g) ready).mp run
  exact ⟨out, callee_trap_bypasses path, by rw [v1_to_lime, lime_to_core g, eq]⟩

example : ¬ Admitted { site returns with continuation := [.bin .i64 .add] } (.call saved []) := by
  intro h
  have mismatch := h.2
  change (none : Option (List NumType)) = some [.int .i32] at mismatch
  cases mismatch

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine
