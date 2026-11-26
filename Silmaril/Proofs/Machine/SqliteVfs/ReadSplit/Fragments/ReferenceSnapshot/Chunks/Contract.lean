module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (readFragments)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot (ReadsSnapshot)

/-- A nonempty prefix's actual returned state and cumulative end offset
determine where the suffix contract starts. -/
theorem readsSnapshot_append_iff {State : Type} (handler : Handler State)
    (snapshot : Bytes) (handle : Handle) (start : State) (offset count : Nat)
    (prefixRest suffix : List Nat) :
    ReadsSnapshot handler snapshot handle start offset (count :: (prefixRest ++ suffix)) ↔
      ReadsSnapshot handler snapshot handle start offset (count :: prefixRest) ∧
        ReadsSnapshot handler snapshot handle
          (readFragments handler handle start offset count prefixRest).file
          (offset + count + prefixRest.sum) suffix := by
  induction prefixRest generalizing start offset count with
  | nil =>
    change (ReadResult snapshot offset count (handler start (.read handle offset count)).1 ∧
      ReadsSnapshot handler snapshot handle (handler start (.read handle offset count)).2
        (offset + count) suffix) ↔
      (ReadResult snapshot offset count (handler start (.read handle offset count)).1 ∧ True) ∧
        ReadsSnapshot handler snapshot handle (handler start (.read handle offset count)).2
          (offset + count) suffix
    simp
  | cons next tail ih =>
    let call := handler start (.read handle offset count)
    change (ReadResult snapshot offset count call.1 ∧
      ReadsSnapshot handler snapshot handle call.2 (offset + count) (next :: (tail ++ suffix))) ↔
      (ReadResult snapshot offset count call.1 ∧
        ReadsSnapshot handler snapshot handle call.2 (offset + count) (next :: tail)) ∧
        ReadsSnapshot handler snapshot handle
          (readFragments handler handle call.2 (offset + count) next tail).file
          (offset + count + (next :: tail).sum) suffix
    rw [ih call.2 (offset + count) next]
    simp only [List.sum_cons, Nat.add_assoc, and_assoc]

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Chunks
