module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.RangeLocal.Agreement

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.RangeLocal

/-- Per-call byte contracts and stability of the second range's optional
bytes suffice to compare replies. Each schedule retains its actual endpoint. -/
theorem reads_split_of_suffix_agreement {State : Type} (step : Handler State)
    (view : State → FileState) (state : State) (handle : Handle)
    (offset left right : Nat) (rightPositive : 0 < right) :
    let firstReq := Request.read handle offset left
    let secondReq := Request.read handle (offset + left : Nat) right
    let wholeReq := Request.read handle offset (left + right : Nat)
    let first := step state firstReq
    let second := step first.2 secondReq
    let whole := step state wholeReq
    (∀ i, i < right →
      (view state).bytes[offset + left + i]? = (view first.2).bytes[offset + left + i]?) →
    ReadResult (view state).bytes offset left first.1 →
    ReadResult (view first.2).bytes (offset + left) right second.1 →
    ReadResult (view state).bytes offset (left + right) whole.1 →
    combine first.1 second.1 = some whole.1 ∧
      Trace.Valid step state [⟨firstReq, first.1⟩, ⟨secondReq, second.1⟩] second.2 ∧
      Trace.Valid step state [⟨wholeReq, whole.1⟩] whole.2 :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.RangeLocal.reads_split_of_suffix_agreement
    step view state handle offset left right rightPositive

end Silmaril.Machine.SqliteVfs.ReadSplit.RangeLocal
