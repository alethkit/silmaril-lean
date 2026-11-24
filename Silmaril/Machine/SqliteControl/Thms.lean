module

public import Silmaril.Machine.SqliteControl.Defs
import Silmaril.Proofs.Machine.SqliteControl.Refinement

public section

namespace Silmaril.Machine.SqliteControl

/-- Every finite interleaving of the port has an abstract interleaving with the
same visible events, in the same order, and the projected final state. -/
theorem runRefines {cfg after : Config Call} {events : List Event}
    (h : Run CallStep cfg events after) : Run Step (erase cfg) events (erase after) :=
  Silmaril.Proofs.Machine.SqliteControl.runRefines h

end Silmaril.Machine.SqliteControl
