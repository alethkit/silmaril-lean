module

public import Silmaril.Formats.SExp.Family.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Interp.Defs

/-!
# AST payload types as WIT value types

The payload types `Silmaril.Formats.PTy` of tagged ASTs (`WitSig`) are a fragment of the WIT
value types of the Component Model (`WIT.ValType`):

| `PTy` | WIT |
| --- | --- |
| `bool`, `char`, `string` | `bool`, `char`, `string` |
| `s8`, `u8`, `s16`, `u16`, `s32`, `u32`, `s64`, `u64` | the same integer types |
| `f32`, `f64` | `f32`, `f64` |
| `list t` (`bytes = list u8`) | `list<t>` (`list<u8>`) |
| `fixedList t n` | `list<t, n>` |
| `record fs`, `tuple ts` | `record { fs }`, `tuple<ts>` |
| `variant cs`, `enum cs`, `flags ls` | `variant { cs }`, `enum { cs }`, `flags { ls }` |
| `option t`, `result ok err` | `option<t>`, `result<ok, err>` (either side optional) |

These are exactly the WIT value types without names (`ref`), `map`, resource handles
(`own`, `borrow`), `future`, `stream` and `error-context`: `ofWit` is defined on exactly them
and is a left inverse of `toWit` (`ofWit_toWit`).

`toWit` is that map (for any name and resource types: the image mentions neither), and
`valEquiv E t : PTy.Val t ≃ (toWit t).Interp E` identifies the payload values with the Lean
interpretation of the WIT type (`WIT.ValType.Interp`) in every
environment `E`. A payload vector `PTy.Vals ps` is the WIT tuple of its types (`valsEquiv`).
`Thms`: every image is a simple type (no `future`/`stream`), and `toWit` is injective
(`ofWit_toWit`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.WIT

universe u v

variable {Ref : Type u} {Resource : Type v}

/-- The primitive payload type of a WIT primitive. -/
def ofPrim : WIT.Primitive → PTy
  | .bool => .bool
  | .s8 => .s8 | .u8 => .u8 | .s16 => .s16 | .u16 => .u16
  | .s32 => .s32 | .u32 => .u32 | .s64 => .s64 | .u64 => .u64
  | .f32 => .f32 | .f64 => .f64 | .char => .char | .string => .string

mutual
/-- **The WIT type of a payload type.** -/
def toWit : PTy → WIT.ValType Ref Resource
  | .bool => .prim .bool
  | .s32 => .prim .s32
  | .u32 => .prim .u32
  | .s64 => .prim .s64
  | .u64 => .prim .u64
  | .string => .prim .string
  | .list t => .list (toWit t)
  | .s8 => .prim .s8
  | .u8 => .prim .u8
  | .s16 => .prim .s16
  | .u16 => .prim .u16
  | .f32 => .prim .f32
  | .f64 => .prim .f64
  | .char => .prim .char
  | .fixedList t n => .fixedList (toWit t) n
  | .record fs => .record (toWitFields fs)
  | .tuple ts => .tuple (toWitList ts)
  | .variant cs => .variant (toWitCases cs)
  | .enum cs => .enum cs
  | .option t => .option (toWit t)
  | .result ok err => .result (toWitOpt ok) (toWitOpt err)
  | .flags ls => .flags ls

/-- The WIT types of a payload vector. -/
def toWitList : List PTy → List (WIT.ValType Ref Resource)
  | [] => []
  | t :: ts => toWit t :: toWitList ts

/-- The WIT fields of record fields (names kept). -/
def toWitFields : List (String × PTy) → List (String × WIT.ValType Ref Resource)
  | [] => []
  | (n, t) :: fs => (n, toWit t) :: toWitFields fs

/-- The WIT cases of variant cases (names kept). -/
def toWitCases : List (String × Option PTy) → List (String × Option (WIT.ValType Ref Resource))
  | [] => []
  | (n, o) :: cs => (n, toWitOpt o) :: toWitCases cs

/-- The WIT type of an optional payload. -/
def toWitOpt : Option PTy → Option (WIT.ValType Ref Resource)
  | none => none
  | some t => some (toWit t)
end

mutual
/-- **The payload type of a WIT type**, when it has one: the left inverse of `toWit`
(`ofWit_toWit`). `none` for names, `map`, handles, `future`, `stream` and `error-context`. -/
def ofWit : WIT.ValType Ref Resource → Option PTy
  | .prim p => some (ofPrim p)
  | .list t => (ofWit t).map .list
  | .fixedList t n => (ofWit t).map (.fixedList · n)
  | .record fs => (ofWitFields fs).map .record
  | .tuple ts => (ofWitList ts).map .tuple
  | .variant cs => (ofWitCases cs).map .variant
  | .enum cs => some (.enum cs)
  | .flags ls => some (.flags ls)
  | .option t => (ofWit t).map .option
  | .result ok err => (ofWitOpt ok).bind fun a => (ofWitOpt err).map fun b => .result a b
  | .ref _ | .map _ _ | .own _ | .borrow _ | .future _ | .stream _ | .errorContext => none

/-- `ofWit` on a list of types. -/
def ofWitList : List (WIT.ValType Ref Resource) → Option (List PTy)
  | [] => some []
  | t :: ts => (ofWit t).bind fun a => (ofWitList ts).map (a :: ·)

/-- `ofWit` on record fields. -/
def ofWitFields : List (String × WIT.ValType Ref Resource) → Option (List (String × PTy))
  | [] => some []
  | (n, t) :: fs => (ofWit t).bind fun a => (ofWitFields fs).map ((n, a) :: ·)

/-- `ofWit` on variant cases. -/
def ofWitCases :
    List (String × Option (WIT.ValType Ref Resource)) → Option (List (String × Option PTy))
  | [] => some []
  | (n, o) :: cs => (ofWitOpt o).bind fun a => (ofWitCases cs).map ((n, a) :: ·)

/-- `ofWit` on an optional payload (`some none` for an absent one). -/
def ofWitOpt : Option (WIT.ValType Ref Resource) → Option (Option PTy)
  | none => some none
  | some t => (ofWit t).map some
end

/-- Lists along an equivalence of elements. -/
def listEquiv {α β : Type} (e : α ≃ β) : List α ≃ List β where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv l := by simp [List.map_map]
  right_inv l := by simp [List.map_map]

/-- Fixed-length vectors along an equivalence of elements. -/
def vectorEquiv {α β : Type} (e : α ≃ β) (n : Nat) : Vector α n ≃ Vector β n where
  toFun v := v.map e
  invFun v := v.map e.symm
  left_inv v := by simp [Vector.map_map]
  right_inv v := by simp [Vector.map_map]

mutual
/-- **Payload values are the values of their WIT type**, in every environment. -/
def valEquiv (E : WIT.Env Ref Resource) :
    (t : PTy) → t.Val ≃ (toWit t : WIT.ValType Ref Resource).Interp E
  | .bool => Equiv.refl Bool
  | .s32 => Equiv.refl Int32
  | .u32 => Equiv.refl UInt32
  | .s64 => Equiv.refl Int64
  | .u64 => Equiv.refl UInt64
  | .string => Equiv.refl String
  | .list t => listEquiv (valEquiv E t)
  | .s8 => Equiv.refl Int8
  | .u8 => Equiv.refl UInt8
  | .s16 => Equiv.refl Int16
  | .u16 => Equiv.refl UInt16
  | .f32 => Equiv.refl (BitVec 32)
  | .f64 => Equiv.refl (BitVec 64)
  | .char => Equiv.refl Char
  | .fixedList t n => vectorEquiv (valEquiv E t) n
  | .record fs => fieldsEquiv E fs
  | .tuple ts => valsEquiv E ts
  | .variant cs => casesEquiv E cs
  | .enum cs => Equiv.refl (Fin cs.length)
  | .option t => Equiv.optionCongr (valEquiv E t)
  | .result ok err => Equiv.sumCongr (optEquiv E ok) (optEquiv E err)
  | .flags ls => Equiv.refl (BitVec ls.length)

/-- **A payload vector is the WIT tuple of its types.** -/
def valsEquiv (E : WIT.Env Ref Resource) : (ps : List PTy) →
    PTy.Vals ps ≃
      WIT.ValType.InterpList E (toWitList (Ref := Ref) (Resource := Resource) ps)
  | [] => Equiv.refl Unit
  | t :: ps => Equiv.prodCongr (valEquiv E t) (valsEquiv E ps)

/-- Record field values are the values of the WIT record. -/
def fieldsEquiv (E : WIT.Env Ref Resource) : (fs : List (String × PTy)) →
    PTy.FieldVals fs ≃
      WIT.ValType.InterpFields E (toWitFields (Ref := Ref) (Resource := Resource) fs)
  | [] => Equiv.refl Unit
  | (_, t) :: fs => Equiv.prodCongr (valEquiv E t) (fieldsEquiv E fs)

/-- Variant case values are the values of the WIT variant. -/
def casesEquiv (E : WIT.Env Ref Resource) : (cs : List (String × Option PTy)) →
    PTy.CaseVals cs ≃
      WIT.ValType.InterpCases E (toWitCases (Ref := Ref) (Resource := Resource) cs)
  | [] => Equiv.refl Empty
  | (_, o) :: cs => Equiv.sumCongr (optEquiv E o) (casesEquiv E cs)

/-- Optional payload values are the values of the optional WIT type. -/
def optEquiv (E : WIT.Env Ref Resource) : (o : Option PTy) →
    PTy.OptVal o ≃
      WIT.ValType.InterpOpt E (toWitOpt (Ref := Ref) (Resource := Resource) o)
  | none => Equiv.refl Unit
  | some t => valEquiv E t
end

end Silmaril.Wasm.Game.HandleAccept.Wit
