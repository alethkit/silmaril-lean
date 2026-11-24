module

import Init.Data.SInt

@[expose] public section

/-! # SQLite file-control validation fragment

One live connection with a real mutex, one already-open private-cache database,
and one forwarding opcode (1001). A scheduler picks one thread and one step
at a time. The VFS supplies a result and its projected effect on the busy count.
-/

namespace Silmaril.Machine.SqliteControl

abbrev Thread := Nat

structure Shared where
  owner : Option Thread := none
  busyCount : Int32 := 0

structure Config (Local : Type) where
  shared : Shared
  threads : Thread → Local

def Config.advance {Local : Type} (cfg : Config Local) (tid : Thread)
    (localState : Local) (shared : Shared := cfg.shared) : Config Local :=
  ⟨shared, fun other => if other = tid then localState else cfg.threads other⟩

/-- The signed callback status is passed through verbatim, including errors.
The busy count is the only callback effect in the observation model. -/
structure VfsReply where
  status : Int32
  busyAfter : Int32
  deriving DecidableEq, Repr

inductive Input where
  | tick
  | reply (result : VfsReply)

inductive Event where
  | acquired (tid : Thread)
  | fileControl (tid : Thread) (reply : VfsReply)
  | restoredBusy (tid : Thread) (value : Int32)
  | released (tid : Thread)
  | returned (tid : Thread) (status : Int32)
  deriving DecidableEq, Repr

/-- Each participating thread executes one call. An idle thread executes none. -/
inductive Phase where
  | idle
  | acquire
  | vfs
  | restore (saved status : Int32)
  | release (status : Int32)
  | returnResult (status : Int32)
  | done

def step (cfg : Config Phase) (tid : Thread) (input : Input) :
    Option (Event × Config Phase) :=
  match cfg.threads tid, input with
  | .acquire, .tick =>
    if cfg.shared.owner = none then
      some (.acquired tid, cfg.advance tid .vfs {cfg.shared with owner := some tid})
    else none
  | .vfs, .reply reply =>
    if cfg.shared.owner = some tid then
      some (.fileControl tid reply, cfg.advance tid (.restore cfg.shared.busyCount reply.status)
        {cfg.shared with busyCount := reply.busyAfter})
    else none
  | .restore saved status, .tick =>
    if cfg.shared.owner = some tid then
      some (.restoredBusy tid saved, cfg.advance tid (.release status)
        {cfg.shared with busyCount := saved})
    else none
  | .release status, .tick =>
    if cfg.shared.owner = some tid then
      some (.released tid, cfg.advance tid (.returnResult status) {cfg.shared with owner := none})
    else none
  | .returnResult status, .tick => some (.returned tid status, cfg.advance tid .done)
  | _, _ => none

/-- Call-level instructions and the local values live at each program point of
the admitted C branch. The cache entry/exit boundaries are silent. -/
inductive Call where
  | idle
  | mutexEnter
  | btreeEnter
  | osFileControl
  | restoreBusy (nSave rc : Int32)
  | btreeLeave (rc : Int32)
  | mutexLeave (rc : Int32)
  | ret (rc : Int32)
  | done

def Call.erase : Call → Phase
  | .idle => .idle
  | .mutexEnter => .acquire
  | .btreeEnter | .osFileControl => .vfs
  | .restoreBusy nSave rc => .restore nSave rc
  | .btreeLeave rc | .mutexLeave rc => .release rc
  | .ret rc => .returnResult rc
  | .done => .done

def erase (cfg : Config Call) : Config Phase :=
  ⟨cfg.shared, fun tid => (cfg.threads tid).erase⟩

/-- Source-order port of the admitted forwarding branch of sqlite3_file_control.
The saved local is read just before dispatch. Reading it and dispatching form
one step at this call boundary. -/
def callStep (cfg : Config Call) (tid : Thread) (input : Input) :
    Option (Option Event × Config Call) :=
  match cfg.threads tid, input with
  | .mutexEnter, .tick =>
    if cfg.shared.owner.isNone then
      some (some (.acquired tid), cfg.advance tid .btreeEnter {cfg.shared with owner := some tid})
    else none
  | .btreeEnter, .tick =>
    if cfg.shared.owner = some tid then some (none, cfg.advance tid .osFileControl) else none
  | .osFileControl, .reply reply =>
    if cfg.shared.owner = some tid then
      let nSave := cfg.shared.busyCount
      let rc := reply.status
      some (some (.fileControl tid reply), cfg.advance tid (.restoreBusy nSave rc)
        {cfg.shared with busyCount := reply.busyAfter})
    else none
  | .restoreBusy nSave rc, .tick =>
    if cfg.shared.owner = some tid then
      some (some (.restoredBusy tid nSave), cfg.advance tid (.btreeLeave rc)
        {cfg.shared with busyCount := nSave})
    else none
  | .btreeLeave rc, .tick =>
    if cfg.shared.owner = some tid then some (none, cfg.advance tid (.mutexLeave rc)) else none
  | .mutexLeave rc, .tick =>
    if cfg.shared.owner = some tid then
      some (some (.released tid), cfg.advance tid (.ret rc) {cfg.shared with owner := none})
    else none
  | .ret rc, .tick => some (some (.returned tid rc), cfg.advance tid .done)
  | _, _ => none

def Step (cfg : Config Phase) (event : Option Event) (after : Config Phase) : Prop :=
  ∃ tid input label, event = some label ∧ step cfg tid input = some (label, after)

def CallStep (cfg : Config Call) (event : Option Event) (after : Config Call) : Prop :=
  ∃ tid input, callStep cfg tid input = some (event, after)

/-- A finite interleaving in which each step selects a thread afresh.
Silent steps contribute no public event. -/
inductive Run {State : Type} (next : State → Option Event → State → Prop) :
    State → List Event → State → Prop where
  | done (cfg : State) : Run next cfg [] cfg
  | more {cfg middle after : State} {event : Option Event} {rest : List Event} :
      next cfg event middle → Run next middle rest after → Run next cfg (event.toList ++ rest) after

end Silmaril.Machine.SqliteControl
