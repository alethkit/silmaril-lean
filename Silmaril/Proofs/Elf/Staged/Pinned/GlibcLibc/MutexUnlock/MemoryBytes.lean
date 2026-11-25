module

public import Silmaril.X86.Ext.Semantics
public import Silmaril.X86.MemoryModel.Tso.Defs

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.MemoryBytes

open Silmaril.X86 (Byte Word)
open Silmaril.X86.Ext (loadN leBytes leValue leValue_leBytes)
open Silmaril.Process (Memory)

private theorem value_lt (bytes : List Byte) :
    leValue bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => decide
  | cons byte bytes ih =>
    change byte.toNat + 256 * leValue bytes < 256 ^ (bytes.length + 1)
    rw [Nat.pow_succ]
    have byte_lt : byte.toNat < 256 := byte.isLt
    omega

private theorem equal_of_value {left right : List Byte} (size : left.length = right.length)
    (value : leValue left = leValue right) : left = right := by
  induction left generalizing right with
  | nil => simpa using size.symm
  | cons head rest ih =>
    cases right with
    | nil => simp at size
    | cons head' rest' =>
      change head.toNat + 256 * leValue rest = head'.toNat + 256 * leValue rest' at value
      have leftBound : head.toNat < 256 := head.isLt
      have rightBound : head'.toNat < 256 := head'.isLt
      have headEq : head = head' := BitVec.eq_of_toNat_eq (by omega)
      have tailEq : leValue rest = leValue rest' := by omega
      exact congrArg₂ List.cons headEq (ih (by simpa using size) tailEq)

/-- Recover the original byte list when the load fits in a machine word. -/
theorem bytes_of_load {memory : Memory} {address value : Word} {length : Nat}
    (fits : length ≤ 8) (load : loadN memory address length = some value) :
    memory.readBytes address.toNat length = some (leBytes value length) := by
  cases read : memory.readBytes address.toNat length with
  | none => simp [loadN, read] at load
  | some bytes =>
    have len : bytes.length = length := Memory.readWith_length read
    have encoding : BitVec.ofNat 64 (leValue bytes) = value := by
      simpa only [loadN, read, Option.map_some, Option.some.injEq] using load
    have bound : leValue bytes < 2 ^ (8 * length) := by
      have small := value_lt bytes
      rw [len] at small
      rw [Nat.pow_mul]
      exact small
    have wide : leValue bytes < 2 ^ 64 :=
      lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega))
    have valueNat : leValue bytes = value.toNat := by
      have projected := congrArg BitVec.toNat encoding
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wide] using projected
    have exactBytes : bytes = leBytes value length := by
      apply equal_of_value (by simp [len])
      rw [leValue_leBytes, ← valueNat, Nat.mod_eq_of_lt bound]
    exact congrArg some exactBytes

open Silmaril.X86.MemoryModel.Tso (readMem)

theorem readBacking_eq_fifoRead (bytes : Silmaril.Process.ByteMemory) (start length : Nat) :
    Memory.readBacking bytes start length = readMem (fun address => bytes.get? address) start length := by
  induction length generalizing start with
  | zero => rfl
  | succ length previous =>
    simp only [Memory.readBacking, readMem, previous]
    cases bytes.get? start <;>
      cases readMem (fun address => bytes.get? address) (start + 1) length <;> rfl

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.MemoryBytes
