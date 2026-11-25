module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Thms
import Silmaril.Machine.SqliteVfs.Thms

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ChangingSnapshot

open Silmaril.Machine.SqliteVfs

private def initial : FileState := ⟨[10, 20], some .readOnly, 0⟩
private def handle : Handle := ⟨0⟩

/-- Use the bounded handler's reply for the current snapshot, then change its
observable bytes after every read. This deliberately violates ReadLaw. -/
private def changingRead : Handler (FileState × Nat) := fun state request =>
  let (reply, next) := readOnly 8 state.1 request
  match request with
  | .read .. => (reply, { next with bytes := [10, 99] }, state.2 + 1)
  | _ => (reply, next, state.2)

/-- Every admitted live read has the correct reply for its own input bytes. -/
private theorem input_reply (state : FileState × Nat) (token : Handle) (offset count : Int)
    (live : (state.1.mode token).isNone = false) (admitted : ReadRange offset count) :
    ReadResult state.1.bytes offset.toNat count.toNat
      (changingRead state (.read token offset count)).1 := by
  let reply := (readOnly 8 state.1 (.read token offset count)).1
  change ReadResult state.1.bytes offset.toNat count.toNat reply
  have law :
      if (state.1.mode token).isNone then reply = .error .invalidHandle
      else if ReadRange offset count then ReadResult state.1.bytes offset.toNat count.toNat reply
      else reply = .error .invalidRange :=
    ((readOnly_lawful 8).2.1.read state.1 token offset count).2
  simpa only [live, Bool.false_eq_true, ite_false, admitted, ite_true] using law

private theorem does_not_preserve_view : ¬ ReadLaw changingRead Prod.fst := by
  intro law
  have same := (law.read (initial, 0) handle 0 1).1
  have bytes := congrArg FileState.bytes same
  exact (by decide : ([10, 99] : Bytes) ≠ [10, 20]) bytes

example :
    let afterFirst := (changingRead (initial, 0) (.read handle 0 1)).2
    ReadRange 0 2 ∧ ReadRange 0 1 ∧ ReadRange 1 1 ∧
      (initial.mode handle).isNone = false ∧ (afterFirst.1.mode handle).isNone = false :=
  by decide

/-- Exact per-call replies and equal final views permit different reassembled
buffers when the two reads use different intermediate snapshots. -/
private theorem reassembly_counterexample :
    let start := (initial, 0)
    let split := readFragments changingRead handle start 0 1 [1]
    let request := Request.read handle 0 2
    let whole := changingRead start request
    split.reply = some (.ok [10, 99]) ∧ whole.1 = .ok [10, 20] ∧
      split.file.1 = whole.2.1 ∧ split.reply ≠ some whole.1 ∧
      Trace.Valid changingRead start split.trace split.file ∧
      Trace.Valid changingRead start [⟨request, whole.1⟩] whole.2 :=
  ⟨rfl, rfl, rfl, by
    change some (.ok [10, 99] : ReadReply) ≠ some (.ok [10, 20])
    decide, (read_fragments_trace changingRead handle (initial, 0) 0 1 [1]).1, .cons rfl (.nil _)⟩

example :
    let split := readFragments changingRead handle (initial, 0) 0 1 [1]
    split.trace = [⟨.read handle 0 1, .ok [10]⟩, ⟨.read handle 1 1, .ok [99]⟩] ∧
      split.file.1.bytes = [10, 99] := ⟨rfl, rfl⟩

#print axioms input_reply
#print axioms does_not_preserve_view
#print axioms reassembly_counterexample

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ChangingSnapshot
