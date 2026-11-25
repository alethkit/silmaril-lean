module

import Silmaril.Machine.SqliteVfs.PageRead.ReadTrace.DisjointWrite.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadTrace.DisjointWrite

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def before : FileState := ⟨[10], some .readWrite, 0⟩
private def after : FileState := ⟨[10, 0, 99], some .readWrite, 0⟩
private def page : Page := ⟨⟨0⟩, 3, 2⟩

example : Trace.Valid (readWrite 8) before
    [⟨page.request, .shortRead [0, 0]⟩, ⟨.write page.handle 2 [99], .ok ()⟩,
      ⟨page.request, .shortRead [0, 0]⟩] after :=
  disjoint_write_read_trace page (by decide) rfl
    (show readWrite 8 before (.write page.handle 2 [99]) = (.ok (), after) from rfl)
    (.inr (by decide)) rfl

private def fullBefore : FileState := ⟨[10, 20, 30], some .readWrite, 0⟩
private def fullAfter : FileState := ⟨[10, 20, 99], some .readWrite, 0⟩
private def fullPage : Page := ⟨⟨0⟩, 1, 2⟩

example : Trace.Valid (readWrite 8) fullBefore
    [⟨fullPage.request, .ok [10, 20]⟩, ⟨.write fullPage.handle 2 [99], .ok ()⟩,
      ⟨fullPage.request, .ok [10, 20]⟩] fullAfter :=
  disjoint_write_read_trace fullPage (by decide) rfl
    (show readWrite 8 fullBefore (.write fullPage.handle 2 [99]) = (.ok (), fullAfter) from rfl)
    (.inl (by decide)) rfl

#print axioms disjoint_write_read_trace

end Silmaril.Machine.SqliteVfs.PageRead.ReadTrace.DisjointWrite
