module

public import Silmaril.X86.Concurrency.Sqlite.Release.Defs
import Silmaril.Proofs.X86.Concurrency.Sqlite.Release

@[expose] public section

namespace Silmaril.X86.Concurrency.Sqlite.Release

open Silmaril.Machine.SqliteControl
open Silmaril.X86.MemoryModel.Tso hiding Execution
open Silmaril.X86.MemoryModel

/-- Every confined TSO release run projects to the abstract SQLite release. -/
theorem confined_sound (tid lock : Nat) (busy rc : Int32) :
    Sound .fifo id (IsRelease tid lock) (releaseProjection tid lock busy)
      (releaseFootprint lock) (confined tid lock busy rc) :=
  Silmaril.Proofs.X86.Concurrency.Sqlite.Release.confined_sound tid lock busy rc

/-- An SC release matches the same abstract transition through empty-buffer embedding. -/
theorem sc_release_matches {initial last : Silmaril.X86.MemoryModel.Tso.Mem} {tid lock : Nat} {busy rc : Int32}
    (startsLocked : initial lock = some 1)
    (path : Tso.Execution SCStep initial [releaseEvent tid lock] last) :
    (releaseProjection tid lock busy).observe (model := .fifo)
      ⟨[releaseEvent tid lock], xembed last⟩ ∈
      Layer.behaviors .control (releaseInput tid busy rc) :=
  Silmaril.Proofs.X86.Concurrency.Sqlite.Release.sc_release_matches startsLocked path

/-- The concrete lock-byte program has an SC run and a matching abstract release. -/
theorem sc_release_witness :
    let initial : Tso.Mem := fun a => some (if a = 0 then 1 else 0)
    let final := writeMem initial 0 [0]
    MemorySemantics.sc.Executes initial ⟨[releaseEvent 0 0], final⟩ ∧
      ([Event.released 0], (⟨none, 0⟩ : Shared)) ∈
        Layer.behaviors .control (releaseInput 0 0 0) :=
  Silmaril.Proofs.X86.Concurrency.Sqlite.Release.sc_release_witness

/-- Release publishes the owner’s forwarded payload when peers have no pending writes to it. -/
theorem release_publishes {s t : XState Nat} {tid lock payload : Nat}
    (separate : payload ≠ lock) (confined : PeerBuffersAvoid s tid payload)
    (releases : XWeakStep s (releaseEvent tid lock) t) :
    t.memory payload = viewMem s tid payload :=
  Silmaril.Proofs.X86.Concurrency.Sqlite.Release.release_publishes separate confined releases

/-- A peer’s pending lock write can refute observation inclusion for top. -/
theorem top_unsound (allowed : XState Nat → Config Phase → Set Nat) :
    ¬ Sound .fifo id (IsRelease 0 0) (releaseProjection 0 0 0)
      allowed ⊤ :=
  Silmaril.Proofs.X86.Concurrency.Sqlite.Release.top_unsound allowed

/-- The bottom proposal is sound because it supplies no input pairs. -/
theorem bottom_sound {I : Type} {layer : Layer} (model : MemorySemantics)
    (initial : I → model.Initial) (admitted : I → Sqlite.Execution model → Prop)
    (p : Projection layer model.Label model.Final) (allowed : I → layer.Input → Set Nat) :
    Sound model initial admitted p allowed ⊥ :=
  Silmaril.Proofs.X86.Concurrency.Sqlite.Release.bottom_sound model initial admitted p allowed

/-- An admitted run forwards 42 before release and commits it at the release boundary. -/
theorem pending_owner_witness :
    let initial := enqueue (xembed (Tid := Nat) fun a => some (if a = 0 then 1 else 0)) 0 1 [42]
    (initial, releaseInput 0 0 0) ∈ confined 0 0 0 0 ∧
      ∃ run, MemorySemantics.fifo.Executes initial run ∧ IsRelease 0 0 initial run ∧
        initial.memory 1 = some 0 ∧ viewMem initial 0 1 = some 42 ∧
        run.final.memory 1 = some 42 ∧ run.final.buffer 0 = [] :=
  Silmaril.Proofs.X86.Concurrency.Sqlite.Release.pending_owner_witness

/-- Restricting a sound proposal preserves soundness. -/
theorem sound_downward {I : Type} {layer : Layer} {model : MemorySemantics}
    {initial : I → model.Initial} {admitted : I → Sqlite.Execution model → Prop}
    {p : Projection layer model.Label model.Final} {allowed : I → layer.Input → Set Nat}
    {smaller larger : Proposal I layer} (included : smaller ⊆ larger)
    (sound : Sound model initial admitted p allowed larger) : Sound model initial admitted p allowed smaller :=
  Silmaril.Proofs.X86.Concurrency.Sqlite.Release.sound_downward included sound

/-- Union of sound proposals is sound under the same interpretation. -/
theorem sound_union {I : Type} {layer : Layer} {model : MemorySemantics}
    {initial : I → model.Initial} {admitted : I → Sqlite.Execution model → Prop}
    {p : Projection layer model.Label model.Final} {allowed : I → layer.Input → Set Nat}
    {left right : Proposal I layer} (leftSound : Sound model initial admitted p allowed left)
    (rightSound : Sound model initial admitted p allowed right) : Sound model initial admitted p allowed (left ∪ right) :=
  Silmaril.Proofs.X86.Concurrency.Sqlite.Release.sound_union leftSound rightSound

end Silmaril.X86.Concurrency.Sqlite.Release
