module

import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Session
import Silmaril.Wasm.Execution.Core.Intrinsic.Call.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.Thms
import Silmaril.Wasm.Validation.Check.Validate

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

private def signature : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩
private def closed : DefType := (Context.rollGroup {} signature)[0]'(by decide +kernel)
private theorem closedOk : TyOk {} closed := TyOk.check_sound (by decide +kernel)
private theorem expands : Expand closed (.func (.cons .i32 .nil) .nil) := Expand.iff.mpr rfl

private def body (extra : Bool) : Code [.i32] [] [] :=
  if extra then .seq .nop (.seq .unreachable .done) else .seq .unreachable .done

private def raw (extra : Bool) : Func := ⟨⟨0⟩, [], (body extra).erase⟩
private def calleeInst : ModuleInst := { types := [closed] }
private def calleeContext : Context := { types := [closed] }
private def entry (extra : Bool) : FuncInst Unit := ⟨closed, calleeInst, .wasm (raw extra)⟩
private def store (versions : List Bool) : Store Unit := { funcs := versions.map entry }

private theorem calleeOk (versions : List Bool) : ModuleInstOk (store versions) calleeInst calleeContext :=
  ModuleInstOk.mk (k := 0) (by simpa [calleeInst] using closedOk) .nil .nil .nil .nil .nil
    (by simp [calleeInst]) .nil (by simp [calleeInst]) (by simp [calleeInst]) (by simp [calleeInst]) (by simp)

private theorem storeOk (versions : List Bool) : StoreOk (store versions) := by
  constructor <;> try (solve | simp [store])
  intro fn membership
  obtain ⟨extra, _, rfl⟩ := List.mem_map.mp membership
  have codeOk : FuncOk calleeContext (raw extra) closed := .mk rfl expands .nil ((body extra).sound rfl)
  exact .wasm closedOk (calleeOk versions) rfl codeOk (Sub.refl _ (k := .def) trivial closed)

private def callerContext : Context := { funcs := [closed] }

private def caller (versions : List Bool) (address : Nat) (extra : Bool)
    (found : versions[address]? = some extra) : World Unit callerContext where
  store := store versions
  moduleInst := { funcs := [address] }
  storeOk := storeOk versions
  moduleOk := ModuleInstOk.mk (k := 0) (by simp) .nil .nil
    (.cons (ExternAddrOk.func (fi := entry extra) (by simp [store, found])) .nil) .nil .nil
    (by simp) .nil (by simp) (by simp) (by simp) (by simp)

private def call (versions : List Bool) (address : Nat) (extra : Bool)
    (found : versions[address]? = some extra) : DirectCall (caller versions address extra found) [.i32] [] :=
  ⟨⟨0⟩, address, entry extra, [], ⟨0⟩, body extra, calleeContext, calleeOk versions,
    rfl, by simp [caller, store, found], expands, rfl⟩

private theorem traps {versions : List Bool} {address : Nat} {extra : Bool}
    (found : versions[address]? = some extra) (args : Values [.i32]) :
    (call versions address extra found).runFor args 2 = some none := by
  cases args with
  | cons bits tail => cases tail; cases extra <;> rfl

example : raw false ≠ raw true := by
  intro equal
  have length := congrArg (fun fn : Func => fn.body.length) equal
  exact (by decide : (1 : Nat) ≠ 2) length

example : FunEquiv Eq (profile neverFail) noHost (store [false, true]) 0 1 :=
  ((call [false, true] 0 false rfl).entry_eq (call [false, true] 1 true rfl)
    fun args => ⟨2, 2, none, traps rfl args, traps rfl args⟩).funEquiv

example : ModuleEquiv Eq (profile neverFail) noHost (store [false]) (store [true]) := by
  apply EntryAgreement.moduleEquiv
  intro address accepted
  cases address with
  | zero =>
    exact (call [false] 0 false rfl).entry_eq (call [true] 0 true rfl)
      fun args => ⟨2, 2, none, traps rfl args, traps rfl args⟩
  | succ address =>
    obtain ⟨_, left | right⟩ := accepted
    · obtain ⟨_, _, _, found, _, _⟩ := left
      simp [store] at found
    · obtain ⟨_, _, _, found, _, _⟩ := right
      simp [store] at found

#print axioms DirectCall.invoke_sound
#print axioms DirectCall.invokeOk_iff
#print axioms DirectCall.invocations_eq_iff
#print axioms DirectCall.invoke_not_diverges
#print axioms DirectCall.entry_eq
#print axioms EntryAgreement.moduleEquiv
#print axioms Silmaril.Wasm.Abstract.InstSession.denUD_core3SemD_eq_of_related_stores
#print axioms Silmaril.Wasm.Abstract.InstSession.compEquiv_of_equal_replacement_sessions_iff
