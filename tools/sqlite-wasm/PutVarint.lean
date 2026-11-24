module

public import SqliteWasm.NineByteVarint
public import SqliteWasm.PutVarintCheck
public import SqliteWasm.PutVarintTwoByte

@[expose] public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (CGlobalType Expand Ty)
open SqliteWasmArtifact
open ThreeByte (args callFrame)
open ThreeByte.Symbolic (quotedHelper)

set_option maxRecDepth 131072

namespace PutVarint

/-- Runtime premises selected by the input value. Inline calls use the wrapper's memory.
Forwarded calls use the helper's memory and i32 global. Only the ordinary helper path
requires a scratch range. -/
def MemoryPremises {H : Type} (s : Store H) (fn : Func) (fi : FuncInst H)
    (ptr sp : BitVec 32) (value : UInt64) (address : Nat) (mem : MemInst) : Prop :=
  if value.toNat < 16384 then
    s.mem? (callFrame fi.module fn ptr value) ⟨0⟩ = some (address, mem) ∧
      ptr.toNat + (Varint.encode value).length ≤ mem.bytes.size
  else
    ∃ (helperAddress : Nat) (helper : FuncInst H) (globalAddress : Nat) (globalType : CGlobalType),
      s.func? (callFrame fi.module fn ptr value) ⟨547⟩ = some (helperAddress, helper) ∧
      helper.code = .wasm quotedHelper ∧
      Expand helper.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)) ∧
      s.mem? (callFrame helper.module quotedHelper ptr value) ⟨0⟩ = some (address, mem) ∧
      s.global? (callFrame helper.module quotedHelper ptr value) ⟨0⟩ =
        some (globalAddress, ⟨globalType, .i32 sp⟩) ∧
      (if value.toNat < 2 ^ 56 then
        OrdinaryVarint.Buffers mem.bytes ptr sp (Varint.encode value).length
      else NineByteVarint.Bounds mem.bytes ptr)

/-- The exact byte image for all widths. Scratch is written only on the ordinary helper path. -/
def outputBytes (bytes : ByteArray) (ptr sp : BitVec 32) (value : UInt64) : ByteArray :=
  if 16384 ≤ value.toNat ∧ value.toNat < 2 ^ 56 then
    ThreeByte.outputBytes bytes ptr sp value
  else Memory.writeSlice bytes ptr.toNat (Varint.encode value).data

end PutVarint

/-- All UInt64 values on the quoted reactor encoder. The active branch determines
the required runtime bindings and memory spans and whether scratch is written. -/
theorem putVarint {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {fn : Func} {instanceAddr : Nat} {fi : FuncInst H}
    {ptr sp : BitVec 32} {value : UInt64} {address : Nat} {mem : MemInst}
    (selected : definedFunction? sqlite 530 = some fn)
    (slot : caller.module.funcs[530]? = some instanceAddr)
    (instanceAt : s.funcs[instanceAddr]? = some fi)
    (code : fi.code = .wasm fn)
    (signature : Expand fi.type (.func (.cons Ty.i32 (.cons Ty.i64 .nil)) (.cons Ty.i32 .nil)))
    (memory : PutVarint.MemoryPremises s fn fi ptr sp value address mem) :
    Steps P host ⟨s, caller, vals (args ptr value) ++ [.plain (.call ⟨530⟩)]⟩
      ⟨s.setMem address { mem with bytes := PutVarint.outputBytes mem.bytes ptr sp value }, caller,
        [constI32 (BitVec.ofNat 32 (Varint.encode value).length)]⟩ := by
  by_cases inline : value.toNat < 16384
  · unfold PutVarint.MemoryPremises at memory
    rw [ite_eq_left inline] at memory
    rw [PutVarint.outputBytes, ite_eq_right (by omega)]
    obtain ⟨mapped, bound⟩ := memory
    by_cases small : value.toNat < 128
    · have width : (Varint.encode value).length = 1 := by simp [encode_one_byte value small]
      rw [width] at bound
      exact putVarint_oneByte selected slot instanceAt code signature small mapped bound
    · have lower : 128 ≤ value.toNat := by omega
      have width : (Varint.encode value).length = 2 := by simp [encode_two value lower inline]
      rw [width] at bound
      exact putVarint_twoByte selected slot instanceAt code signature lower inline mapped bound
  · unfold PutVarint.MemoryPremises at memory
    rw [ite_eq_right inline] at memory
    obtain ⟨helperAddress, helper, globalAddress, globalType, helperBinding, helperCode, helperType,
      mapped, global, bounds⟩ := memory
    have putBinding : s.func? caller ⟨530⟩ = some (instanceAddr, fi) := by
      change (caller.module.funcs[530]?.bind fun a =>
        (s.funcs[a]?).bind fun target => some (a, target)) = _
      simp [slot, instanceAt]
    have forwarded : 16384 ≤ value.toNat := by omega
    by_cases ordinary : value.toNat < 2 ^ 56
    · obtain ⟨width, enters, fits⟩ := OrdinaryVarint.existsWidth value.toNat forwarded ordinary
      have widthEq : (Varint.encode value).length = width := OrdinaryVarint.ordinaryLength value width fits
      rw [ite_eq_left ordinary, widthEq] at bounds
      rw [PutVarint.outputBytes, ite_eq_left ⟨forwarded, ordinary⟩, widthEq]
      exact OrdinaryVarint.putVarint_ordinary selected putBinding helperBinding code helperCode
        signature helperType enters fits mapped global bounds
    · have wide : 2 ^ 56 ≤ value.toNat := Nat.le_of_not_gt ordinary
      rw [ite_eq_right ordinary] at bounds
      rw [PutVarint.outputBytes, ite_eq_right (fun both => ordinary both.2),
        NineByteVarint.encodedLength value wide]
      exact NineByteVarint.putVarint_nineByte selected putBinding helperBinding code helperCode
        signature helperType wide mapped global bounds

#print axioms putVarint

end SqliteWasm
