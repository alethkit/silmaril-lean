module

public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryGrow

open Silmaril.Semantics.SOS
open Execution
open Execution.Runtime (MemInst)

theorem fact {m : MemInst} {a b : State} (h : Outcome m a b) : Edge m a b :=
  Derives.apply (R := (presentation m).rules) (r := ⟨[], (a, b)⟩) ⟨rfl, h⟩ (fun _ h => nomatch h)

theorem invert {m : MemInst} {a b : State} (e : Edge m a b) : Outcome m a b :=
  Derives.least (M := fun j => Outcome m j.1 j.2) e (fun _ hr _ => hr.2)

/-- A successful growth appends exactly `delta` zero-filled pages. -/
theorem grown_bytes {m : MemInst} {delta : BitVec 32} {bytes : ByteArray}
    (edge : Edge m (.request delta) (.grown bytes)) :
    bytes = m.data ++ ⟨Array.replicate (delta.toNat * Memory.pageSize) 0⟩ := by
  cases invert edge with
  | grow delta bytes h => unfold Memory.grow? at h; split at h <;> simp_all

theorem grown_pages {m : MemInst} {delta : BitVec 32} {bytes : ByteArray}
    (edge : Edge m (.request delta) (.grown bytes)) :
    Memory.size bytes = Memory.size m.data + delta.toNat := by
  cases invert edge with
  | grow delta bytes h =>
    simp only [Memory.size, Memory.grow_size _ _ _ _ h]
    rw [Nat.add_mul_div_right _ _ (by decide : 0 < Memory.pageSize)]

end Silmaril.Wasm.Institution.Operational.MemoryGrow
