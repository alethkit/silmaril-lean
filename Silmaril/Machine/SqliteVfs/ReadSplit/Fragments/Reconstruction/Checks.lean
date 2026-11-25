module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction.Thms

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction

open Silmaril.Machine.SqliteVfs

private def handle : Handle := ⟨0⟩
private def state : FileState := ⟨[7], some .readOnly, 0⟩

example {trace : Trace} {finish : FileState}
    (valid : Trace.Valid (readOnly 8) state trace finish)
    (requests : trace.map Exchange.request = fragmentRequests handle 0 [0, 1]) :
    trace = [⟨.read handle 0 0, .error .invalidRange⟩, ⟨.read handle 0 1, .ok [7]⟩] ∧
      finish = state := by
  exact read_fragments_reconstruct (readOnly 8) handle state 0 0 [1] valid requests

private def firstReadReply : Trace → Option ReadReply
  | ⟨.read .., reply⟩ :: _ => some reply
  | _ => none

example {finish : FileState} :
    ¬ Trace.Valid (readOnly 8) state
      [⟨.read handle 0 0, .ok []⟩, ⟨.read handle 0 1, .ok [7]⟩] finish := by
  intro forged
  have same := (read_fragments_reconstruct (readOnly 8) handle state 0 0 [1] forged rfl).1
  exact (by decide : some (ReadReply.ok []) ≠ some (.error .invalidRange))
    (congrArg firstReadReply same)

private def counting : Handler (FileState × Nat) := fun input request =>
  let (reply, next) := readOnly 8 input.1 request
  (reply, next, input.2 + 1)

example {trace : Trace} {finish : FileState × Nat}
    (valid : Trace.Valid counting (state, 5) trace finish)
    (requests : trace.map Exchange.request = fragmentRequests handle 0 [0, 1]) :
    trace = [⟨.read handle 0 0, .error .invalidRange⟩, ⟨.read handle 0 1, .ok [7]⟩] ∧
      finish = (state, 7) :=
  read_fragments_reconstruct counting handle (state, 5) 0 0 [1] valid requests

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Reconstruction
