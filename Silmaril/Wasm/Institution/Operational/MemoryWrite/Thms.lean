module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Defs
public import Silmaril.Wasm.Logic.Memory.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Logic.Core (Region bytesAt)

theorem fact {mem : ByteArray} {a b : State} (h : Outcome mem a b) : Edge mem a b :=
  Derives.apply (R := (presentation mem).rules) (r := ⟨[], (a, b)⟩) ⟨rfl, h⟩ (fun _ h => nomatch h)

theorem invert {mem : ByteArray} {a b : State} (h : Edge mem a b) : Outcome mem a b :=
  Derives.least (M := fun j => Outcome mem j.1 j.2) h (fun _ hr _ => hr.2)

theorem closed {mem : ByteArray} {a b : State} (edge : Edge mem a b) : Admitted mem b := by
  cases invert edge with
  | write _ _ _ h => exact Silmaril.Wasm.Logic.Core.size_store h
  | trap => trivial

theorem read_after_write {mem out : ByteArray} {address word : BitVec 32}
    (edge : Edge mem (.store address word) (.written out)) :
    Memory.load out address.toNat 4 = some word := by
  cases invert edge with
  | write _ _ _ h => exact Silmaril.Wasm.Logic.Core.load_store_same h

theorem disjoint_bytes {mem out : ByteArray} {address word : BitVec 32} {r : Region}
    (edge : Edge mem (.store address word) (.written out))
    (separate : (⟨address.toNat, 4⟩ : Region).Disjoint r) :
    bytesAt out r = bytesAt mem r := by
  cases invert edge with
  | write _ _ _ h => exact Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint h separate

theorem store_none_iff {mem : ByteArray} {address word : BitVec 32} :
    Memory.store mem address.toNat (count := 4) word = none ↔ mem.size < address.toNat + 4 := by
  by_cases bound : address.toNat + 4 ≤ mem.size <;>
    simp [Memory.store, Memory.writeBytes, bound, Nat.not_lt.mpr, Nat.lt_of_not_ge]

end Silmaril.Wasm.Institution.Operational.MemoryWrite
