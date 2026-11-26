module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Defs
public import Silmaril.Wasm.Logic.Memory.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Logic.Core (Region bytesAt)

theorem fact_at {mem : ByteArray} {offset : Nat} {a b : State} (h : OutcomeAt mem offset a b) : EdgeAt mem offset a b :=
  Derives.apply (R := (presentationAt mem offset).rules) (r := ⟨[], (a, b)⟩) ⟨rfl, h⟩ (fun _ h => nomatch h)

theorem invert_at {mem : ByteArray} {offset : Nat} {a b : State} (h : EdgeAt mem offset a b) : OutcomeAt mem offset a b :=
  Derives.least (M := fun j => OutcomeAt mem offset j.1 j.2) h (fun _ hr _ => hr.2)

theorem closed_at {mem : ByteArray} {offset : Nat} {a b : State} (edge : EdgeAt mem offset a b) : Admitted mem b := by
  cases invert_at edge with
  | write _ _ _ h => exact Silmaril.Wasm.Logic.Core.size_store h
  | trap => trivial

theorem read_after_write_at {mem out : ByteArray} {offset : Nat} {address word : BitVec 32}
    (edge : EdgeAt mem offset (.store address word) (.written out)) :
    Memory.load out (address.toNat + offset) 4 = some word := by
  cases invert_at edge with
  | write _ _ _ h => exact Silmaril.Wasm.Logic.Core.load_store_same h

theorem disjoint_bytes_at {mem out : ByteArray} {offset : Nat} {address word : BitVec 32} {r : Region}
    (edge : EdgeAt mem offset (.store address word) (.written out))
    (separate : (⟨address.toNat + offset, 4⟩ : Region).Disjoint r) :
    bytesAt out r = bytesAt mem r := by
  cases invert_at edge with
  | write _ _ _ h => exact Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint h separate

theorem store_none_iff_at {mem : ByteArray} {offset : Nat} {address word : BitVec 32} :
    Memory.store mem (address.toNat + offset) (count := 4) word = none ↔ mem.size < address.toNat + offset + 4 := by
  by_cases bound : address.toNat + offset + 4 ≤ mem.size <;>
    simp [Memory.store, Memory.writeBytes, bound, Nat.not_lt.mpr, Nat.lt_of_not_ge]

theorem store_trap_iff_at {mem : ByteArray} {offset : Nat} {address word : BitVec 32} :
    EdgeAt mem offset (.store address word) .trap ↔ mem.size < address.toNat + offset + 4 :=
  ⟨fun edge => match invert_at edge with | .trap _ _ bound => bound,
    fun bound => fact_at (.trap address word bound)⟩

theorem fact {mem : ByteArray} {a b : State} (h : Outcome mem a b) : Edge mem a b :=
  fact_at h

theorem invert {mem : ByteArray} {a b : State} (h : Edge mem a b) : Outcome mem a b :=
  invert_at h

theorem closed {mem : ByteArray} {a b : State} (edge : Edge mem a b) : Admitted mem b :=
  closed_at edge

theorem read_after_write {mem out : ByteArray} {address word : BitVec 32}
    (edge : Edge mem (.store address word) (.written out)) :
    Memory.load out address.toNat 4 = some word :=
  read_after_write_at edge

theorem disjoint_bytes {mem out : ByteArray} {address word : BitVec 32} {r : Region}
    (edge : Edge mem (.store address word) (.written out))
    (separate : (⟨address.toNat, 4⟩ : Region).Disjoint r) :
    bytesAt out r = bytesAt mem r :=
  disjoint_bytes_at edge separate

theorem store_none_iff {mem : ByteArray} {address word : BitVec 32} :
    Memory.store mem address.toNat (count := 4) word = none ↔ mem.size < address.toNat + 4 :=
  store_none_iff_at (offset := 0)

end Silmaril.Wasm.Institution.Operational.MemoryWrite
