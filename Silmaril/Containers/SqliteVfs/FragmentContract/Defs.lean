module

public import Silmaril.Machine.SqliteVfs.Defs

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.FragmentContract

open Silmaril.Machine.SqliteVfs

/-- A completed read reply can be checked using only its typed exchange and
the specified reference bytes. Negative signed request fields are rejected
before conversion to natural indices. -/
def ReplyMatchesSnapshot (snapshot : Bytes) (exchange : Exchange) : Prop :=
  match exchange with
  | ⟨.read _ offset count, reply⟩ =>
      0 ≤ offset ∧ 0 ≤ count ∧ ReadResult snapshot offset.toNat count.toNat reply
  | _ => False

end Silmaril.Containers.SqliteVfs.FragmentContract
