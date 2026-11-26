module

public import Silmaril.Machine.SqliteVfs.ReadInterval.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies.Agreement

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies

open Silmaril.Machine.SqliteVfs.ReadInterval (presentCount)

/-- A checked matching reply gives the requested-range agreement needed
for the first call. A short reply also needs a matching present-prefix
count, and the remainder is checked on the actual returned state. -/
theorem cons_of_matching_reply {State : Type} (handler : Handler State)
    (view : State → Bytes) (reference : Bytes) (handle : Handle)
    (start : State) (offset count : Nat) (rest : List Nat)
    (admitted : ReadRange offset count) {referenceReply : ReadReply}
    (referenceRead : ReadResult reference offset count referenceReply)
    (actualRead : ReadResult (view start) offset count (handler start (.read handle offset count)).1)
    (sameReply : referenceReply = (handler start (.read handle offset count)).1)
    (shortCount : reference.length < offset + count →
      presentCount reference offset count = presentCount (view start) offset count)
    (remaining : ReadsAgreeingViews handler view reference handle
      (handler start (.read handle offset count)).2 (offset + count) rest) :
    ReadsAgreeingViews handler view reference handle start offset (count :: rest) :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies.cons_of_matching_reply
    handler view reference handle start offset count rest admitted referenceRead actualRead
    sameReply shortCount remaining

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Replies
