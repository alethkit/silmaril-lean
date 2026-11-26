module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews

open Silmaril.Machine.SqliteVfs

/-- Each actual call has a positive size, satisfies the contract on its
current view and agrees with the reference on its requested optional bytes. -/
def ReadsAgreeingViews {State : Type} (handler : Handler State)
    (view : State → Bytes) (reference : Bytes) (handle : Handle)
    (state : State) (offset : Nat) : List Nat → Prop
  | [] => True
  | count :: rest =>
    let call := handler state (.read handle offset count)
    0 < count ∧
      (∀ i, i < count → reference[offset + i]? = (view state)[offset + i]?) ∧
      ReadResult (view state) offset count call.1 ∧
      ReadsAgreeingViews handler view reference handle call.2 (offset + count) rest

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews
