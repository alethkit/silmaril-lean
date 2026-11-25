module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot

open Silmaril.Machine.SqliteVfs

/-- Each listed call returns the contracted reply on the requested range of
one reference snapshot. The contract follows actual returned handler states. -/
def ReadsSnapshot {State : Type} (step : Handler State) (snapshot : Bytes)
    (handle : Handle) (state : State) (offset : Nat) : List Nat → Prop
  | [] => True
  | count :: rest =>
    let call := step state (.read handle offset count)
    ReadResult snapshot offset count call.1 ∧
      ReadsSnapshot step snapshot handle call.2 (offset + count) rest

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot
