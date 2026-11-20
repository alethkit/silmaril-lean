module

public import Silmaril.Wasm.Profiles.Defs
public import Silmaril.Wasm.Models.Syntax.Thms
public import Silmaril.Wasm.ModuleParts.Thms

public section

namespace Silmaril.Wasm.Profiles

open Models

namespace Typing

variable {Raw Index : Type} {ok : Raw → Index → Prop}

@[expose] def declaredEquiv : Declared ok ≃ SomeChecked ok where
  toFun term := ⟨term.val.2, term.val.1, term.property⟩
  invFun term := ⟨(term.2.val, term.1), term.2.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem declaredEquiv_index (term : Declared ok) : (declaredEquiv term).1 = term.val.2 := rfl

theorem Declared.forget_surjective : Function.Surjective (Declared.forget (ok := ok)) := by
  rintro ⟨raw, index, typed⟩
  exact ⟨⟨(raw, index), typed⟩, rfl⟩

theorem Declared.forget_eq_iff (left right : Declared ok) :
    left.forget = right.forget ↔ left.val.1 = right.val.1 := Subtype.ext_iff

end Typing

theorem wasm1_func_iff (ctx : HasTyping.Context Wasm1) (fn : Function Wasm1) :
    (∃ sig, HasTyping.funcOk ctx fn sig) ↔ V1.Validation.FuncValid ctx fn := Iff.rfl

theorem lime_func_iff (ctx : HasTyping.Context Lime) (fn : Function Lime) :
    (∃ sig, HasTyping.funcOk ctx fn sig) ↔ Lime1.Validation.FuncValid ctx fn := Iff.rfl

theorem SomeTypedModule.checked_surjective {W : Type} [HasSyntax W] [HasTyping W] [HasIntrinsic W] :
    Function.Surjective (SomeTypedModule.checked (W := W)) := by
  rintro ⟨iface, raw, valid⟩
  obtain ⟨typed, rfl⟩ := HasIntrinsic.moduleLift valid
  exact ⟨⟨iface, typed⟩, rfl⟩

theorem SomeTypedFunction.checked_surjective {W : Type} [HasSyntax W] [HasTyping W] [HasIntrinsic W]
    (ctx : HasTyping.Context W) : Function.Surjective (SomeTypedFunction.checked (W := W) (ctx := ctx)) := by
  rintro ⟨sig, raw, valid⟩
  obtain ⟨typed, rfl⟩ := HasIntrinsic.functionLift valid
  exact ⟨⟨sig, typed⟩, rfl⟩

noncomputable def wasm3ModuleEquiv (iface : HasTyping.Interface Wasm3) :
    Validation.Intrinsic.Module.Erasure iface ≃ CheckedModule Wasm3 iface :=
  Validation.Intrinsic.Module.equiv iface

noncomputable def wasm3FunctionEquiv (ctx : HasTyping.Context Wasm3) (sig : HasTyping.FuncType Wasm3) :
    Validation.Intrinsic.Function.Erasure ctx sig ≃ CheckedFunction Wasm3 ctx sig :=
  Validation.Intrinsic.Function.equiv ctx sig

def CoreImage.ofLE {S T : FeatureSet} (sub : S ≤ T) : CoreImage S ↪ CoreImage T where
  toFun mod := ⟨mod.val, module_mono sub mod.val mod.property⟩
  inj' := fun _ _ eq => Subtype.ext (congrArg (fun mod : CoreImage T => mod.val) eq)

@[expose] def Strict.toFunctional : Module Strict ↪ Module Functional where
  toFun mod := ⟨mod.val, module_mono ((remove_le functional .exn).trans functional_le_functionalMutGC) _ mod.property.1⟩
  inj' := fun _ _ eq => Subtype.ext (congrArg (fun mod : Module Functional => mod.val) eq)

@[simp] theorem Strict.toFunctional_val (mod : Module Strict) : (toFunctional mod).val = mod.val := rfl

@[simp] theorem Strict.check?_complete (mod : Module Strict) : check? mod.val = some mod := by
  cases mod with | mk raw valid => exact dite_eq_left valid

theorem Strict.check?_sound {raw : Wasm.Module} {mod : Module Strict} (ok : check? raw = some mod) :
    raw = mod.val := by
  unfold check? at ok
  split at ok
  · exact congrArg (fun term : Module Strict => term.val) (Option.some.inj ok)
  · cases ok

/-- Exactly the well-typed Core image at this interface. The inverse retains
the same Core AST, without choosing an intrinsic typing derivation. -/
@[expose] def Strict.checkedEquiv (iface : HasTyping.Interface Strict) :
    CheckedModule Strict iface ≃ { mod : Wasm.Module // accepts mod ∧ Validation.ModuleOk mod iface } where
  toFun mod := ⟨mod.val.val, mod.val.property, mod.property⟩
  invFun mod := ⟨⟨mod.val, mod.property.1⟩, mod.property.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem Strict.checkedEquiv_val {iface} (mod : CheckedModule Strict iface) :
    (checkedEquiv iface mod).val = mod.val.val := rfl

@[simp] theorem Strict.parts_toCore (mod : Module Strict) : (parts mod).toCore = mod.val := mod.val.toCore_split

end Silmaril.Wasm.Profiles
