module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution

theorem fact_at {bytes : ByteArray} {offset : Nat} {a b : State} (h : RuleInstanceAt bytes offset ⟨[], (a, b)⟩) :
    EdgeAt bytes offset a b :=
  Derives.apply (R := (presentationAt bytes offset).rules) (r := ⟨[], (a, b)⟩) h (fun _ h => nomatch h)

theorem invert_at {bytes : ByteArray} {offset : Nat} {a b : State} (edge : EdgeAt bytes offset a b) :
    RuleInstanceAt bytes offset ⟨[], (a, b)⟩ := Proofs.invert_at edge

theorem load_none_iff_at {bytes : ByteArray} {offset : Nat} {address : BitVec 32} :
    Memory.load bytes (address.toNat + offset) 4 = none ↔ bytes.size < address.toNat + offset + 4 :=
  Proofs.load_none_iff_at

theorem load_trap_iff_at {bytes : ByteArray} {offset : Nat} {address : BitVec 32} :
    EdgeAt bytes offset (.load address) .trap ↔ bytes.size < address.toNat + offset + 4 :=
  ⟨fun edge => match invert_at edge with | .loadTrap _ bound => bound,
    fun bound => fact_at (.loadTrap address bound)⟩

theorem fact {bytes : ByteArray} {a b : State} (h : RuleInstance bytes ⟨[], (a, b)⟩) :
    Edge bytes a b :=
  fact_at h

theorem invert {bytes : ByteArray} {a b : State} (edge : Edge bytes a b) :
    RuleInstance bytes ⟨[], (a, b)⟩ :=
  invert_at edge

theorem load_none_iff {bytes : ByteArray} {address : BitVec 32} :
    Memory.load bytes address.toNat 4 = none ↔ bytes.size < address.toNat + 4 :=
  load_none_iff_at (offset := 0)

end Silmaril.Wasm.Institution.Operational.MemoryQuery
