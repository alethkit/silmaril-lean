module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallFrame.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame.Proofs

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (AdminInstr Frame FuncAddr Value)

private theorem instructions_map {I J : Type} (emit : Locals.Op → I) (out : Locals.Op → J)
    (translate : I → J) (agrees : ∀ op, translate (emit op) = out op) (ret dead : I) (p : Program) :
    (p.instructions emit ret dead).map translate = p.instructions out (translate ret) (translate dead) := by
  cases p <;> simp [Program.instructions, List.map_map, agrees]

private theorem op_toLime (op : Locals.Op) :
    (Locals.v1Instr op).toLime = Locals.limeInstr op := by
  cases op with
  | value v => rcases v with ⟨t, bits⟩; cases t <;> rfl
  | _ => rfl

private theorem op_toCore (op : Locals.Op) :
    (Locals.limeInstr op).toCore = Locals.coreInstr op := by
  cases op with
  | value v => rcases v with ⟨t, bits⟩; cases t <;> rfl
  | _ => rfl

private theorem program_toLime (p : Program) :
    (p.instructions Locals.v1Instr .return_ .unreachable).map Wasm.V1.Instr.toLime =
      p.instructions Locals.limeInstr .return_ .unreachable :=
  instructions_map _ _ _ op_toLime _ _ _

private theorem program_toCore (p : Program) :
    (p.instructions Locals.limeInstr .return_ .unreachable).map Wasm.Lime1.Instr.toCore =
      p.instructions Locals.coreInstr .return_ .unreachable :=
  instructions_map _ _ _ op_toCore _ _ _

theorem function_toLime (fn : Callee) : fn.v1Func.toLime = fn.limeFunc := by
  simp [Callee.v1Func, Callee.limeFunc, Wasm.V1.Func.toLime, Wasm.V1.Expr.toLime_eq_map, program_toLime]

theorem function_toCore (fn : Callee) : fn.limeFunc.toCore = fn.coreFunc := by
  simp [Callee.limeFunc, Callee.coreFunc, Wasm.Lime1.Func.toCore, Wasm.Lime1.Expr.toCore_eq_map, program_toCore]

theorem allocated_toLime {H : Type} {s : Wasm.V1.Execution.Store H} {address : FuncAddr} {fn : Callee}
    (h : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.v1Func)) :
    (s.mapCode Wasm.V1.Func.toLime).funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc) := by
  simp [Runtime.Store.mapCode, List.getElem?_map, h, Runtime.FuncInst.mapCode, function_toLime]

theorem allocated_toCore {H : Type} {s : Wasm.Lime1.Execution.Store H} {address : FuncAddr} {fn : Callee}
    (h : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc)) :
    s.toCore.funcs[address.value]? = some fn.coreInstance := by
  simp [Runtime.Store.toCore, List.getElem?_map, h, Runtime.FuncInst.toCore, function_toCore, Callee.coreInstance]

private theorem legacy_body_toLime (body : Body) :
    Wasm.V1.Execution.codeToLime (legacyBody Locals.v1Instr .return_ .unreachable body) =
      legacyBody Locals.limeInstr .return_ .unreachable body := by
  cases body with
  | trap => rfl
  | code p =>
    change Wasm.V1.Execution.codeToLime (Wasm.V1.Execution.expression _) = _
    rw [Wasm.V1.Execution.map_expression, Wasm.V1.Expr.toLime_eq_map, program_toLime]
    rfl

private theorem legacy_exit_toLime (ready : Exit) :
    Wasm.V1.Execution.codeToLime (legacyExit Wasm.V1.Execution.value .return_ ready) =
      legacyExit Wasm.Lime1.Execution.value .return_ ready := by
  cases ready with
  | values xs => exact Wasm.V1.Execution.map_values xs
  | ret xs =>
    change Wasm.V1.Execution.codeToLime (Wasm.V1.Execution.values xs ++ [.source .return_]) = _
    rw [Wasm.V1.Execution.codeToLime_append, Wasm.V1.Execution.map_values]
    rfl
  | trap => rfl

private theorem v1_values (vs : List Value) :
    vs.map Wasm.V1.Execution.value = Wasm.V1.Execution.values vs := rfl

private theorem lime_values (vs : List Value) :
    vs.map Wasm.Lime1.Execution.value = Wasm.Lime1.Execution.values vs := rfl

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (address : FuncAddr)
    (fn : Callee) (q : State) :
    (v1Config s caller address fn q).toLime =
      limeConfig (s.mapCode Wasm.V1.Func.toLime) caller address fn q := by
  have code : Wasm.V1.Execution.codeToLime (v1Code address fn q) = limeCode address fn q := by
    cases q <;>
      simp only [v1Code, limeCode, legacyCode, v1_values, lime_values, Wasm.V1.Execution.codeToLime_append,
        Wasm.V1.Execution.codeToLime_cons, Wasm.V1.Execution.codeToLime_nil, Wasm.V1.Execution.map_values,
        AdminInstr.map, legacy_body_toLime, legacy_exit_toLime, List.map_nil]
  exact congrArg (fun xs => (⟨s.mapCode Wasm.V1.Func.toLime, caller, xs⟩ : Wasm.Lime1.Execution.Config H)) code

private theorem append_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (a b : List Wasm.Lime1.Execution.Admin) :
    Wasm.Lime1.Execution.Admin.listToCore s (a ++ b) =
      Wasm.Lime1.Execution.Admin.listToCore s a ++ Wasm.Lime1.Execution.Admin.listToCore s b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [Wasm.Lime1.Execution.Admin.listToCore, ih, List.append_assoc]

private theorem core_values {H : Type} (s : Wasm.Lime1.Execution.Store H) (values : List Value) :
    Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values values) =
      Core.vals (values.map Value.toCore) := by
  induction values with
  | nil => rfl
  | cons v vs ih =>
    change Wasm.Lime1.Execution.Admin.toCore s (Wasm.Lime1.Execution.value v) ++
      Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values vs) = _
    rw [ih]
    rcases v with ⟨t, bits⟩
    cases t <;> rfl

private theorem core_expression {H : Type} (s : Wasm.Lime1.Execution.Store H) (code : List Wasm.Lime1.Instr) :
    Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.expression code) =
      Core.expression (code.map Wasm.Lime1.Instr.toCore) := by
  induction code with
  | nil => rfl
  | cons instruction rest ih =>
    change .plain instruction.toCore :: Wasm.Lime1.Execution.Admin.listToCore s
      (Wasm.Lime1.Execution.expression rest) = Core.expression ((instruction :: rest).map _)
    rw [ih]
    rfl

private theorem legacy_body_toCore {H : Type} (s : Wasm.Lime1.Execution.Store H) (body : Body) :
    Wasm.Lime1.Execution.Admin.listToCore s (legacyBody Locals.limeInstr .return_ .unreachable body) =
      coreBody body := by
  cases body with
  | trap => rfl
  | code p =>
    change Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.expression _) = _
    rw [core_expression, program_toCore]
    rfl

private theorem legacy_exit_toCore {H : Type} (s : Wasm.Lime1.Execution.Store H) (ready : Exit) :
    Wasm.Lime1.Execution.Admin.listToCore s (legacyExit Wasm.Lime1.Execution.value .return_ ready) =
      coreExit ready := by
  cases ready with
  | values xs => exact core_values s xs
  | ret xs =>
    change Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values xs ++ [.source .return_]) = _
    rw [append_core, core_values]
    rfl
  | trap => rfl

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} (caller : Frame)
    {address : FuncAddr} {fn : Callee}
    (allocated : s.funcs[address.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    (q : State) :
    (limeConfig s caller address fn q).toCore = coreConfig s.toCore caller address fn q := by
  have type : s.funcDefType address = fn.type.toDefType := by
    simp [Runtime.Store.funcDefType, allocated, Runtime.FuncInst.type]
  have code : Wasm.Lime1.Execution.Admin.listToCore s (limeCode address fn q) = coreCode address fn q := by
    cases q <;>
      simp only [limeCode, legacyCode, coreCode, lime_values, append_core, core_values,
        Wasm.Lime1.Execution.Admin.listToCore, Wasm.Lime1.Execution.Admin.toCore,
        legacy_body_toCore, legacy_exit_toCore, type, List.append_nil, List.map_nil]
  exact congrArg (fun xs => (⟨s.toCore, caller.toCore, xs⟩ : Core.Config H)) code

theorem run_iff {C : Type} {fn : Callee} (render : State → C) (native : C → C → Prop)
    (sound : ∀ {a b}, Edge fn a b → native (render a) (render b))
    (readback : ∀ {a b}, Admitted fn a → native (render a) b → ∃ out, Edge fn a out ∧ b = render out)
    {a : State} {b : C} (ready : Admitted fn a) :
    Relation.ReflTransGen native (render a) b ↔
      ∃ out, Runs fn a out ∧ Admitted fn out ∧ b = render out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, guard, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback guard step
      exact ⟨out, path.tail edge, CallFrame.closed guard edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift render (fun _ _ h => sound h) _ _ path

end Silmaril.Wasm.Institution.Operational.CallFrame.Proofs
