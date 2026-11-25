module

public import Silmaril.Machine.SqliteVfs.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit

/-- Reassemble adjacent reads of one file view. Both replies must expose
buffers. A short segment makes the reassembled reply short. -/
def combine : ReadReply → ReadReply → Option ReadReply
  | .ok left, .ok right => some (.ok (left ++ right))
  | .ok left, .shortRead right
  | .shortRead left, .ok right
  | .shortRead left, .shortRead right => some (.shortRead (left ++ right))
  | _, _ => none

end Silmaril.Machine.SqliteVfs.ReadSplit
