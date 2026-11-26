module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ChunkReferences.Agreement

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ChunkReferences

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (readFragments)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)

/-- Two adjacent chunks may use separate references that agree locally
with one target. The nonempty prefix determines the suffix state and offset. -/
theorem readsAgreeingViews_iff_of_chunk_references {State : Type} (handler : Handler State)
    (view : State → Bytes) (target firstReference secondReference : Bytes) (handle : Handle)
    (start : State) (offset count : Nat) (prefixRest suffix : List Nat)
    (firstAgreement : ∀ i, i < count + prefixRest.sum →
      target[offset + i]? = firstReference[offset + i]?)
    (secondAgreement : ∀ i, i < suffix.sum →
      target[offset + count + prefixRest.sum + i]? = secondReference[offset + count + prefixRest.sum + i]?) :
    ReadsAgreeingViews handler view target handle start offset (count :: (prefixRest ++ suffix)) ↔
      ReadsAgreeingViews handler view firstReference handle start offset (count :: prefixRest) ∧
        ReadsAgreeingViews handler view secondReference handle
          (readFragments handler handle start offset count prefixRest).file
          (offset + count + prefixRest.sum) suffix :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ChunkReferences.readsAgreeingViews_iff_of_chunk_references
    handler view target firstReference secondReference handle start offset count
    prefixRest suffix firstAgreement secondAgreement

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.ChunkReferences
