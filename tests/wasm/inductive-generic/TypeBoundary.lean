module

import Silmaril.Wasm.Validation.Generic.SSA.Thms
import Silmaril.Wasm.Validation.Intrinsic.ReifyThms
import Silmaril.Wasm.SSA.Translate.Thms
import Silmaril.Wasm.SSA.Fragment.Thms
import Silmaril.SSA.Isotope.Types.Thms

open Silmaril Silmaril.Wasm Silmaril.Isotope.LambdaSSA
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Generic
open Silmaril.Wasm.Generic.SSA

private inductive Op where
  | one | ten | add | divU

private def Op.wasm : Op → SSA.Prim
  | .one => .op (.const (.i32 1))
  | .ten => .op (.const (.i32 10))
  | .add => .op (.bin (.int .i32 .add))
  | .divU => .opT (.bin (.int .i32 (.div .unsigned)))

private abbrev Code := Silmaril.Ty IntType
private abbrev FreeCode := FreeTy TypeFeatures.all IntType
private def i32 : Code := .base .i32

private instance : HasTy Op Code where
  src
    | .one | .ten => .unit
    | .add | .divU => .product i32 (.product i32 .unit)
  trg
    | .one | .ten | .add => i32
    | .divU => .coprod i32 .unit

private instance : HasTy Op FreeCode where
  src op := Silmaril.Ty.toFree (instrSrc (τ := Code) op)
  trg op := Silmaril.Ty.toFree (instrTrg (τ := Code) op)

private def source : Boundary Code where
  arg
    | .base type => some (.num (.int type))
    | _ => none
  result
    | .base type => some [.num (.int type)]
    | .unit => some []
    | _ => none
  trap := .unit

private def target : Boundary FreeCode where
  arg type := source.arg type.toTy
  result type := source.result type.toTy
  trap := .unit rfl

private def encoding : TypeMap Op Code FreeCode :=
  ⟨Silmaril.Ty.toFree, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

private theorem forward : BoundaryMap encoding source target :=
  ⟨fun type => congrArg source.arg (FreeTy.toTy_toFree type),
    fun type => congrArg source.result (FreeTy.toTy_toFree type), rfl⟩

private def decoding : TypeMap Op FreeCode Code :=
  ⟨FreeTy.toTy, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl,
    fun op => FreeTy.toTy_toFree (instrSrc (τ := Code) op),
    fun op => FreeTy.toTy_toFree (instrTrg (τ := Code) op)⟩

private theorem backward : BoundaryMap decoding target source := ⟨fun _ => rfl, fun _ => rfl, rfl⟩

private def inc : Region Op := .let₁ (.op .one .unit)
  (.let₁ (.op .add (.pair (.var 1) (.pair (.var 0) .unit))) (.br 0 (.var 0)))

private def divide : Region Op := .let₁ (.op .ten .unit)
  (.case (.op .divU (.pair (.var 0) (.pair (.var 1) .unit))) (.br 0 (.var 0)) (.br 1 .unit))

private theorem inc_typed : inc.HasType [i32] [i32, Silmaril.Ty.unit] :=
  .let₁ (.op .unit) (.let₁ (.op (.pair (.var rfl) (.pair (.var rfl) .unit))) (.br rfl (.var rfl)))

private theorem divide_typed : divide.HasType [i32] [i32, Silmaril.Ty.unit] :=
  .let₁ (.op .unit) (.case (.op (.pair (.var rfl) (.pair (.var rfl) .unit)))
    (.br rfl (.var rfl)) (.br rfl .unit))

private def raw : Wasm.Module :=
  { types := [⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩]
    funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩]⟩, ⟨⟨0⟩, [], [.localGet ⟨0⟩]⟩]
    exports := [⟨"inc", .func ⟨0⟩⟩, ⟨"div", .func ⟨1⟩⟩] }

private def checked := (Intrinsic.Reify.reify? raw).get (by decide +kernel)
private def header := (Typed.Module.ofIntrinsic checked.typed).header

private def fn (code : Region Op) (typed : code.HasType [i32] [i32, Silmaril.Ty.unit]) :
    AtCore Op Code source header.scope (header.signatures[0]'(by decide +kernel)) :=
  ⟨⟨.here, by decide⟩, [i32], i32, [.i32], [.i32], rfl, rfl, rfl, code, typed⟩

private def module_ : Typed.Module (AtCore Op Code source) checked.interface :=
  ⟨header, .cons (fn inc inc_typed) (.cons (fn divide divide_typed) .nil)⟩

example : (module_.map (AtCore.retype forward)).forget AtCore.syntax = module_.forget AtCore.syntax :=
  retype_module_syntax forward module_

example : ((module_.map (AtCore.retype forward)).map (AtCore.retype backward)) = module_ :=
  retype_module_roundtrip forward backward FreeTy.toTy_toFree module_

example : source.arg (.product i32 i32) = none := rfl
example : target.result (.coprod rfl (.base .i32) (.unit rfl)) = none := rfl

private def eraseTm : Tm Op → Tm SSA.Prim
  | .var index => .var index
  | .op op arg => .op op.wasm (eraseTm arg)
  | .let₁ value body => .let₁ (eraseTm value) (eraseTm body)
  | .pair left right => .pair (eraseTm left) (eraseTm right)
  | .unit => .unit
  | .let₂ value body => .let₂ (eraseTm value) (eraseTm body)
  | .inl value => .inl (eraseTm value)
  | .inr value => .inr (eraseTm value)
  | .case value left right => .case (eraseTm value) (eraseTm left) (eraseTm right)
  | .abort value => .abort (eraseTm value)

private def eraseRegion : Region Op → Region SSA.Prim
  | .br label arg => .br label (eraseTm arg)
  | .case value left right => .case (eraseTm value) (eraseRegion left) (eraseRegion right)
  | .let₁ value body => .let₁ (eraseTm value) (eraseRegion body)
  | .let₂ value body => .let₂ (eraseTm value) (eraseRegion body)
  | .cfg entry count blocks => .cfg (eraseRegion entry) count (fun slot => eraseRegion (blocks slot))

private def executable (region : Region Op) : SSA.SFunc := ⟨[.i32], some .i32, eraseRegion region⟩

example : executable ((module_.map (AtCore.retype forward)).defs.get .here).code =
    SSA.compileFunc SSA.exampleInc := rfl

example : executable ((module_.map (AtCore.retype forward)).defs.get (.there .here)).code =
    SSA.compileFunc SSA.exampleDiv := rfl

example : (executable ((module_.map (AtCore.retype forward)).defs.get .here).code).Run [.i32 41]
    (.ret (some (.i32 42))) := SSA.compileFunc_iff.mpr SSA.exampleInc_run

example : (executable ((module_.map (AtCore.retype forward)).defs.get (.there .here)).code).Run
    [.i32 0] .trap := SSA.compileFunc_iff.mpr
      (SSA.FragFunc.eval_sound (f := SSA.exampleDiv) (fuel := 10) (by decide))

#print axioms TypeMap.region
#print axioms AtCore.retype
#print axioms retype_module_syntax
#print axioms retype_module_roundtrip
