module
public import Silmaril.Formats.Sqlite.VirtualTable.Thms
public import Silmaril.Formats.Sqlite.VirtualTable.Backed.Defs
import Silmaril.Proofs.Formats.Sqlite.VirtualTable.Backed

public section
namespace Silmaril.Formats.Sqlite.VirtualTable.Backed

theorem candidates_honest (snapshot : Snapshot 1) (dir : Direction) (lo hi : Int64) :
    Honest (query dir lo hi) (plan dir) snapshot (candidates snapshot dir lo) :=
  Proofs.Formats.Sqlite.VirtualTable.Backed.candidates_honest snapshot dir lo hi

theorem startQuery_eq (snapshot : Snapshot 1) (dir : Direction) (lo hi : Int64) :
    (table snapshot).startQuery (query dir lo hi) =
      .ok (plan dir, .scanning (candidates snapshot dir lo)) :=
  Proofs.Formats.Sqlite.VirtualTable.Backed.startQuery_eq snapshot dir lo hi

theorem query_correct (snapshot : Snapshot 1) (dir : Direction) (lo hi : Int64) :
    (table snapshot).run (query dir lo hi) = .ok ((query dir lo hi).reference snapshot) :=
  Proofs.Formats.Sqlite.VirtualTable.Backed.query_correct snapshot dir lo hi

end Silmaril.Formats.Sqlite.VirtualTable.Backed
