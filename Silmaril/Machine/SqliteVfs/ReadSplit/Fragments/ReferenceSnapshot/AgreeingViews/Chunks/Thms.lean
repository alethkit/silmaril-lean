module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Chunks.Agreement

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (readFragments)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)

/-- Split or recombine the per-call agreement at a nonempty executed
prefix. The suffix uses that prefix's returned state and end offset. -/
theorem readsAgreeingViews_append_iff {State : Type} (handler : Handler State) (view : State → Bytes)
    (reference : Bytes) (handle : Handle) (start : State) (offset count : Nat)
    (prefixRest suffix : List Nat) :
    ReadsAgreeingViews handler view reference handle start offset (count :: (prefixRest ++ suffix)) ↔
      ReadsAgreeingViews handler view reference handle start offset (count :: prefixRest) ∧
        ReadsAgreeingViews handler view reference handle
          (readFragments handler handle start offset count prefixRest).file
          (offset + count + prefixRest.sum) suffix :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Chunks.readsAgreeingViews_append_iff
    handler view reference handle start offset count prefixRest suffix

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Chunks
