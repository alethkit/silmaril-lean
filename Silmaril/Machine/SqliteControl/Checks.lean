module

import Silmaril.Machine.SqliteControl.Thms

namespace Silmaril.Machine.SqliteControl

private def start : Config Call :=
  ⟨{ busyCount := 7 }, fun tid => if tid < 2 then .mutexEnter else .idle⟩

private def ioError : VfsReply := ⟨266, 8⟩
private def ok : VfsReply := ⟨0, 8⟩

private def schedule (cfg : Config Call) :
    List (Thread × Input) → Option (List Event × Config Call)
  | [] => some ([], cfg)
  | (tid, input) :: tail => do
    let (event, middle) ← callStep cfg tid input
    let (events, after) ← schedule middle tail
    some (event.toList ++ events, after)

-- A blocking enter has no transition while another caller owns the mutex.
example : (schedule start [(0, .tick), (1, .tick)]).isNone = true := rfl

-- A callback result can advance only an owner waiting for VFS dispatch.
example : (schedule start [(0, .tick), (1, .reply ok)]).isNone = true := rfl

-- The second caller can acquire after release but before the first caller returns.
-- Both restore the same busy count, independently of their callback status.
example :
    (schedule start [
      (0, .tick), (0, .tick), (0, .reply ioError), (0, .tick), (0, .tick), (0, .tick),
      (1, .tick), (0, .tick),
      (1, .tick), (1, .reply ok), (1, .tick), (1, .tick), (1, .tick), (1, .tick)
    ]).map (fun (events, cfg) => (events, cfg.shared.owner, cfg.shared.busyCount)) =
    some ([
      .acquired 0, .fileControl 0 ioError, .restoredBusy 0 7, .released 0,
      .acquired 1, .returned 0 266, .fileControl 1 ok, .restoredBusy 1 7,
      .released 1, .returned 1 0
    ], none, 7) := rfl

end Silmaril.Machine.SqliteControl
