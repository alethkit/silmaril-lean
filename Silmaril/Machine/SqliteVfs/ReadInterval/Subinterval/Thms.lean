module

public import Silmaril.Machine.SqliteVfs.ReadInterval.Defs
import Init.Omega

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadInterval.Subinterval

/-- In one contiguous view, the present prefix of an outer interval
determines the present prefix of any subinterval within it. -/
theorem presentCount_subinterval (bytes : Bytes) (offset size skip count : Nat)
    (within : skip + count ≤ size) :
    presentCount bytes (offset + skip) count =
      min count (presentCount bytes offset size - skip) := by
  unfold presentCount
  omega

end Silmaril.Machine.SqliteVfs.ReadInterval.Subinterval
