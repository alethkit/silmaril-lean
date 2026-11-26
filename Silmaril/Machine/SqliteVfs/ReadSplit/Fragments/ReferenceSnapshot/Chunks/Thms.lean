module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Chunks.Contract

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (readFragments)

/-- A nonempty prefix's actual returned state and cumulative end offset
determine where the suffix contract starts. -/
theorem readsSnapshot_append_iff {State : Type} (handler : Handler State)
    (snapshot : Bytes) (handle : Handle) (start : State) (offset count : Nat)
    (prefixRest suffix : List Nat) :
    ReadsSnapshot handler snapshot handle start offset (count :: (prefixRest ++ suffix)) ↔
      ReadsSnapshot handler snapshot handle start offset (count :: prefixRest) ∧
        ReadsSnapshot handler snapshot handle
          (readFragments handler handle start offset count prefixRest).file
          (offset + count + prefixRest.sum) suffix :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Chunks.readsSnapshot_append_iff
    handler snapshot handle start offset count prefixRest suffix

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Chunks
