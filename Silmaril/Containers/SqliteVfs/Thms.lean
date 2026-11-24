module

public import Silmaril.Containers.SqliteVfs.Defs
import Silmaril.Proofs.Containers.SqliteVfs.Trace

@[expose] public section

namespace Silmaril.Containers.SqliteVfs

open Silmaril.Machine.SqliteVfs

/-- The finite executions are exactly valid exchanges with an optional final,
unanswered receive. The characterization includes the ending machine state. -/
theorem exec_iff {State : Type} {handler : Handler State} {start : State}
    {events : List Event} {finish : Phase State} :
    (machine handler).Exec Mach.seqPolicy (.idle start) events finish ↔
      ∃ trace current, Trace.Valid handler start trace current ∧
        ((events = encode trace ∧ finish = .idle current) ∨
          ∃ request, events = encode trace ++ [.recv request] ∧ finish = .pending current request) :=
  Proofs.Containers.SqliteVfs.exec_iff

/-- The runtime can wait for input exactly after the completed exchanges of
a valid trace, including the empty trace. -/
theorem blocked_iff {State : Type} {handler : Handler State} {start : State}
    {events : List Event} :
    (runtime handler).beh start (.blocked events) ↔
      ∃ trace finish, Trace.Valid handler start trace finish ∧ events = encode trace :=
  Proofs.Containers.SqliteVfs.blocked_iff

end Silmaril.Containers.SqliteVfs
