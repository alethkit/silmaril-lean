module

import Silmaril.Machine.SqliteVfs.PageRead.ReadTrace.Thms
import Silmaril.Machine.SqliteVfs.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadTrace

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def start : FileState := ⟨[10], some .readWrite, 0⟩
private def grown : FileState := ⟨[10, 0, 99], some .readWrite, 0⟩
private def page : Page := ⟨⟨0⟩, 1, 2⟩
private def write : Exchange := ⟨.write page.handle 2 [99], .ok ()⟩
private def truncate : Exchange := ⟨.truncate page.handle 1, .ok ()⟩
private def shortRead : Exchange := ⟨page.request, .shortRead [10, 0]⟩

example : readWrite 8 grown page.request = (.ok [10, 0], grown) := rfl

example : Trace.Valid (readWrite 8) start [shortRead, write, truncate, shortRead] start := by
  have middle : Trace.Valid (readWrite 8) start [write, truncate] start :=
    .cons (show readWrite 8 start write.request = (write.response, grown) from rfl)
      (.cons (show readWrite 8 grown truncate.request = (truncate.response, start) from rfl)
        (.nil _))
  exact reads_around_trace (readWrite_lawful 8).2.1 middle page (by decide) rfl rfl (fun _ _ => rfl)

#print axioms reads_around_trace

end Silmaril.Machine.SqliteVfs.PageRead.ReadTrace
