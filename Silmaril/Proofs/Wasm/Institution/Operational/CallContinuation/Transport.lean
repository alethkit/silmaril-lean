module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
public import Silmaril.Wasm.RuntimeMap.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs

open Execution
open Execution.Runtime (Frame FuncAddr Value)

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (q : State) :
    (v1Config s caller addr fn q).toLime =
      limeConfig (s.mapCode Wasm.V1.Func.toLime) caller addr fn q := by
  change (⟨s.mapCode Wasm.V1.Func.toLime, caller,
    Wasm.V1.Execution.codeToLime (v1Code addr fn q)⟩ : Wasm.Lime1.Execution.Config H) = _
  have code (phase : CallFrame.State) : Wasm.V1.Execution.codeToLime (CallFrame.v1Code addr fn phase) =
      CallFrame.limeCode addr fn phase :=
    congrArg (fun c : Wasm.Lime1.Execution.Config H => c.code) (CallFrame.v1_to_lime s caller addr fn phase)
  have nop : Wasm.V1.Instr.toLime .nop = .nop := rfl
  cases q with
  | active phase =>
    simp only [v1Code, limeCode, limeConfig, render, Wasm.V1.Execution.codeToLime_append, code]
    rfl
  | resume stack | done stack =>
    simp [v1Code, limeCode, limeConfig, render, Runtime.AdminInstr.map, nop]
  | trapped stack hasTail =>
    cases hasTail <;> simp [v1Code, limeCode, limeConfig, render, tail, Runtime.AdminInstr.map, nop]

theorem config_toLime_injective (H : Type) :
    Function.Injective (Wasm.V1.Execution.Config.toLime (H := H)) := by
  rintro ⟨s, f, xs⟩ ⟨t, g, ys⟩ eq
  have stores := RuntimeMap.store_mapCode_injective Wasm.V1.Func.toLime_injective
    (congrArg (fun c : Wasm.Lime1.Execution.Config H => c.store) eq)
  have frames : f = g := congrArg (fun c : Wasm.Lime1.Execution.Config H => c.frame) eq
  have codes := RuntimeMap.adminInstr_mapList_injective Wasm.V1.Instr.toLime_injective xs ys
    (congrArg (fun c : Wasm.Lime1.Execution.Config H => c.code) eq)
  cases stores
  cases frames
  cases codes
  rfl

theorem core_append {H : Type} (s : Wasm.Lime1.Execution.Store H)
    (a b : List Wasm.Lime1.Execution.Admin) :
    Wasm.Lime1.Execution.Admin.listToCore s (a ++ b) =
      Wasm.Lime1.Execution.Admin.listToCore s a ++ Wasm.Lime1.Execution.Admin.listToCore s b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [Wasm.Lime1.Execution.Admin.listToCore, ih, List.append_assoc]

theorem core_values {H : Type} (s : Wasm.Lime1.Execution.Store H) (vs : List Value) :
    Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values vs) =
      Core.vals (vs.map Value.toCore) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change Wasm.Lime1.Execution.Admin.toCore s (Wasm.Lime1.Execution.value v) ++
      Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values vs) = _
    rw [ih]
    rcases v with ⟨t, bits⟩
    cases t <;> rfl

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} (caller : Frame)
    {addr : FuncAddr} {fn : CallFrame.Callee}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc)) (q : State) :
    (limeConfig s caller addr fn q).toCore = coreConfig s.toCore caller addr fn q := by
  change (⟨s.toCore, caller.toCore, Wasm.Lime1.Execution.Admin.listToCore s (limeCode addr fn q)⟩ :
    Core.Config H) = _
  have code (phase : CallFrame.State) : Wasm.Lime1.Execution.Admin.listToCore s
      (CallFrame.limeCode addr fn phase) = CallFrame.coreCode addr fn phase :=
    congrArg Core.Config.code (CallFrame.lime_to_core caller allocated phase)
  cases q with
  | active phase => simp only [limeCode, render, core_append, code]; rfl
  | resume stack => simp only [limeCode, render, core_append, core_values]; rfl
  | done stack => simp only [limeCode, render, core_values]; rfl
  | trapped stack hasTail =>
    cases hasTail <;> simp only [limeCode, render, core_append, core_values, tail,
      ↓reduceIte, Bool.false_eq_true] <;> rfl

end Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs
