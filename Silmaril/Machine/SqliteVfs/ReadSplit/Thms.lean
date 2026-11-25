module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Snapshot


@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit

/-- Positive adjacent segments inherit admission from their whole read. -/
theorem range_split {offset left right : Nat}
    (whole : ReadRange offset (left + right : Nat))
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    ReadRange offset left ∧ ReadRange (offset + left : Nat) right :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.range_split whole leftPositive rightPositive

/-- Same-snapshot results give the exact whole-range status and padded buffer. -/
theorem read_result_combine {bytes : Bytes} {offset leftCount rightCount : Nat}
    {leftReply rightReply : ReadReply}
    (leftRead : ReadResult bytes offset leftCount leftReply)
    (rightRead : ReadResult bytes (offset + leftCount) rightCount rightReply) :
    ∃ reply, combine leftReply rightReply = some reply ∧
      ReadResult bytes offset (leftCount + rightCount) reply :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.read_result_combine leftRead rightRead

/-- Compare the reassembled reply and final file view of two admitted reads
with one whole read, retaining each actual typed VFS trace. -/
theorem reads_split {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadLaw step view) (state : State) (handle : Handle) {offset left right : Nat}
    (admitted : ReadRange offset (left + right : Nat))
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (live : ((view state).mode handle).isNone = false) :
    let firstReq := Request.read handle offset left
    let secondReq := Request.read handle (offset + left : Nat) right
    let wholeReq := Request.read handle offset (left + right : Nat)
    let first := step state firstReq
    let second := step first.2 secondReq
    let whole := step state wholeReq
    combine first.1 second.1 = some whole.1 ∧
      view second.2 = view whole.2 ∧
      Trace.Valid step state [⟨firstReq, first.1⟩, ⟨secondReq, second.1⟩] second.2 ∧
      Trace.Valid step state [⟨wholeReq, whole.1⟩] whole.2 :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.reads_split law state handle admitted leftPositive rightPositive live

end Silmaril.Machine.SqliteVfs.ReadSplit
