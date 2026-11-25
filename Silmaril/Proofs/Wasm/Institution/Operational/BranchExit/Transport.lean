module

public import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Defs
public import Silmaril.Wasm.Institution.Operational.BranchExit.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.BranchExit.Proofs

open Execution.Core
open Execution.Runtime (Value)

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (f : Execution.Runtime.Frame)
    (ty : Option NumType) (a : State) :
    (v1Config s f ty a).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) f ty a := by
  have branch (vs : List Value) (l : LabelIdx) :
      Wasm.V1.Execution.codeToLime (Wasm.V1.Execution.values vs ++ [.source (.br l)]) =
        Wasm.Lime1.Execution.values vs ++ [.source (.br l)] := by
    rw [Wasm.V1.Execution.codeToLime_append, Wasm.V1.Execution.map_values]
    rfl
  cases a with
  | nested n below payload =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, f,
      [.label ty.toList.length [] [.label n []
        (Wasm.V1.Execution.codeToLime (Wasm.V1.Execution.values (below ++ payload) ++ [.source (.br ⟨1⟩)]))]]⟩ :
      Wasm.Lime1.Execution.Config H) = _
    rw [branch]
    rfl
  | outer below payload =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, f,
      [.label ty.toList.length []
        (Wasm.V1.Execution.codeToLime (Wasm.V1.Execution.values (below ++ payload) ++ [.source (.br ⟨0⟩)]))]⟩ :
      Wasm.Lime1.Execution.Config H) = _
    rw [branch]
    rfl
  | done payload =>
    exact congrArg (fun code => (⟨s.mapCode Wasm.V1.Func.toLime, f, code⟩ : Wasm.Lime1.Execution.Config H))
      (Wasm.V1.Execution.map_values payload)

private theorem core_values_prefix {H : Type} (s : Wasm.Lime1.Execution.Store H)
    (vs : List Value) (tail : List Wasm.Lime1.Execution.Admin) :
    Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values vs ++ tail) =
      vals (vs.map LegacyDivision.liftValue) ++ Wasm.Lime1.Execution.Admin.listToCore s tail := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change Wasm.Lime1.Execution.Admin.toCore s (Wasm.Lime1.Execution.value v) ++
      Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values vs ++ tail) = _
    rw [ih]
    rcases v with ⟨t, bits⟩
    cases t <;> rfl

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Execution.Runtime.Frame)
    (ty : Option NumType) (a : State) :
    (limeConfig s f ty a).toCore = coreConfig s.toCore f.toCore ty a := by
  have branch (vs : List Value) (l : LabelIdx) :
      Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values vs ++ [.source (.br l)]) =
        vals (vs.map LegacyDivision.liftValue) ++ [.plain (.br l)] := by
    rw [core_values_prefix]
    rfl
  cases a with
  | nested n below payload =>
    change (⟨s.toCore, f.toCore, [.label ty.toList.length [] [.label n []
      (Wasm.Lime1.Execution.Admin.listToCore s
        (Wasm.Lime1.Execution.values (below ++ payload) ++ [.source (.br ⟨1⟩)]))]]⟩ : Config H) = _
    rw [branch]
    rfl
  | outer below payload =>
    change (⟨s.toCore, f.toCore, [.label ty.toList.length []
      (Wasm.Lime1.Execution.Admin.listToCore s
        (Wasm.Lime1.Execution.values (below ++ payload) ++ [.source (.br ⟨0⟩)]))]⟩ : Config H) = _
    rw [branch]
    rfl
  | done payload =>
    have code := core_values_prefix s payload []
    rw [List.append_nil] at code
    change _ = vals (payload.map LegacyDivision.liftValue) ++ [] at code
    rw [List.append_nil] at code
    exact congrArg (fun code => (⟨s.toCore, f.toCore, code⟩ : Config H)) code

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop) {ty : Option NumType}
    (sound : ∀ {a b}, Edge ty a b → native (emit a) (emit b))
    (readback : ∀ {a b}, Admitted ty a → native (emit a) b → ∃ out, Edge ty a out ∧ b = emit out)
    {a : State} {b : C} (guard : Admitted ty a) :
    Relation.ReflTransGen native (emit a) b ↔
      ∃ out, Runs ty a out ∧ Admitted ty out ∧ b = emit out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, guard, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, typed, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback typed step
      exact ⟨out, path.tail edge, closed edge typed, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ e => sound e) _ _ path

end Silmaril.Wasm.Institution.Operational.BranchExit.Proofs
