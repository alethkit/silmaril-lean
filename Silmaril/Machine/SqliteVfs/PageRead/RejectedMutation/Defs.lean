module

public import Silmaril.Machine.SqliteVfs.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation

open Silmaril.Machine.SqliteVfs

/-- Hide rejected writes and truncates, retaining all other exchanges. -/
def keep : Exchange → Bool
  | ⟨.write .., .error _⟩ | ⟨.truncate .., .error _⟩ => false
  | _ => true

end Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation
