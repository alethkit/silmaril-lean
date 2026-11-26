module

public import Silmaril.Machine.SqliteVfs.ReadInterval.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadInterval.Presence

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadInterval

/-- Matching contracted replies determine the requested optional bytes.
A matching present-prefix count is needed only for short reads. -/
theorem recover_optional_bytes {before after : Bytes} {offset count : Nat}
    {beforeReply afterReply : ReadReply} (_admitted : ReadRange offset count)
    (beforeRead : ReadResult before offset count beforeReply)
    (afterRead : ReadResult after offset count afterReply)
    (sameReply : beforeReply = afterReply)
    (shortCount : before.length < offset + count →
      presentCount before offset count = presentCount after offset count) :
    ∀ i, i < count → before[offset + i]? = after[offset + i]? :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadInterval.recover_optional_bytes _admitted beforeRead afterRead sameReply shortCount

end Silmaril.Machine.SqliteVfs.ReadInterval
