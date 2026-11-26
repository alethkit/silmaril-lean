module

public import Silmaril.Machine.SqliteVfs.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadInterval

/-- The present bytes of a contiguous backing occupy a prefix of the
requested interval. This counts that prefix before zero padding. -/
def presentCount (bytes : Bytes) (offset count : Nat) : Nat :=
  min count (bytes.length - offset)

end Silmaril.Machine.SqliteVfs.ReadInterval
