module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Execution.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Family

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA

open Silmaril.MLIR.WasmSSA
open Silmaril.Wasm (Instr)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile intBinOp)
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P Q : Profile} {host host' : HostSemantics H}

@[simp] theorem intBodyCode_append {a b : List Admin} :
    IntBodyCode (a ++ b) ↔ IntBodyCode a ∧ IntBodyCode b := by
  simp only [IntBodyCode, List.forall_mem_append]

theorem intBodyCode_vals (vs : List Val) : IntBodyCode (vals vs) := by
  intro a ha
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
  exact .inl (by simp)

private theorem intBodyCode_callRef {c : Admin} (call : c.IsCallRef) : ¬ IntBodyCode [c] := by
  cases c with
  | plain i => cases i <;> simp [Admin.IsCallRef, IntBodyCode, Admin.val?, IntBodyInstr] at *
  | _ => simp_all [Admin.IsCallRef, IntBodyCode, Admin.val?]

theorem intBodyCode_family {a : Admin} (body : IntBodyCode [a]) (active : a.val? = none) :
    famOf a = .parametric ∨ famOf a = .numeric ∨ famOf a = .variable ∨ a = .plain .return_ := by
  rcases body a (by simp) with value | ⟨i, rfl, instr⟩
  · simp [active] at value
  · cases i <;> simp_all [IntBodyInstr, famOf]

private theorem intBodyCode_wrong_family {code : List Admin} {family : Fam}
    (shape : FamShape family code) (notAllowed : family ≠ .parametric ∧ family ≠ .numeric ∧
      family ≠ .variable ∧ family ≠ .control) (body : IntBodyCode code) : False := by
  obtain ⟨args, a, rfl, active, tag⟩ := shape
  rcases intBodyCode_family (intBodyCode_append.mp body).2 active with h | h | h | rfl
  · exact notAllowed.1 (tag.symm.trans h)
  · exact notAllowed.2.1 (tag.symm.trans h)
  · exact notAllowed.2.2.1 (tag.symm.trans h)
  · exact notAllowed.2.2.2 tag.symm

set_option maxHeartbeats 500000 in
/-- An integer body step preserves its instruction fragment and store, and is
independent of the numeric profile and host. The frame may change at a local write. -/
theorem intBody_step {source target : Config H} (step : Step P host source target)
    (body : IntBodyCode source.code) :
    target.store = source.store ∧ IntBodyCode target.code ∧ Step Q host' source target := by
  induction step with
  | parametric h =>
    cases h with
    | selectTrue nz => exact ⟨rfl, intBodyCode_vals [_], .parametric (.selectTrue nz)⟩
    | selectFalse v₁ v₂ ts => exact ⟨rfl, intBodyCode_vals [_], .parametric (.selectFalse v₁ v₂ ts)⟩
    | _ => simp [IntBodyCode, Admin.val?, IntBodyInstr] at body
  | numeric h =>
    cases h with
    | intBinOp eq =>
      exact ⟨rfl, by simp [IntBodyCode, Admin.val?], .numeric (.intBinOp eq)⟩
    | intTestOp => exact ⟨rfl, by simp [IntBodyCode, constI32], .numeric .intTestOp⟩
    | intRelOp => exact ⟨rfl, by simp [IntBodyCode, constI32], .numeric .intRelOp⟩
    | intBinOpTrap eq =>
      rename_i op x y e
      cases op <;> simp [IntBodyCode, Admin.val?, IntBodyInstr, intBinOp] at body eq
    | _ => simp [IntBodyCode, Admin.val?, IntBodyInstr] at body
  | «variable» h =>
    cases h with
    | localGet read => exact ⟨rfl, intBodyCode_vals [_], .variable (.localGet read)⟩
    | localSet bound => exact ⟨rfl, by simp [IntBodyCode], .variable (.localSet bound)⟩
    | _ => simp [IntBodyCode, Admin.val?, IntBodyInstr] at body
  | vector h => exact (intBodyCode_wrong_family (VectorStep.shape h) (by decide) body).elim
  | table h => exact (intBodyCode_wrong_family (TableStep.shape h) (by decide) body).elim
  | memory h => exact (intBodyCode_wrong_family (MemoryStep.shape h) (by decide) body).elim
  | reference h => exact (intBodyCode_wrong_family (RefStep.shape h) (by decide) body).elim
  | aggregate h => exact (intBodyCode_wrong_family (AggregateStep.shape h) (by decide) body).elim
  | ctxtInstrs _ hne ih =>
    simp only [intBodyCode_append] at body ⊢
    obtain ⟨hs, hb, hr⟩ := ih body.1.2
    exact ⟨hs, ⟨⟨body.1.1, hb⟩, body.2⟩, .ctxtInstrs hr hne⟩
  | callRefNull call =>
    exact (intBodyCode_callRef call (fun _ h => body _ (by cases List.mem_singleton.mp h; simp))).elim
  | callRefFunc call _ _ _ _ =>
    exact (intBodyCode_callRef call (fun _ h => body _ (by cases List.mem_singleton.mp h; simp))).elim
  | callRefHost call _ _ _ _ _ =>
    exact (intBodyCode_callRef call (fun _ h => body _ (by cases List.mem_singleton.mp h; simp))).elim
  | callRefHostDiv call _ _ _ _ _ =>
    exact (intBodyCode_callRef call (fun _ h => body _ (by cases List.mem_singleton.mp h; simp))).elim
  | _ =>
    simp only [intBodyCode_append] at body
    simp [IntBodyCode, Admin.val?, IntBodyInstr, throwing] at body

end Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA
