module

import Silmaril.Machine.SqliteVfs.PageRead.ReadFrame.Thms
import Silmaril.Machine.SqliteVfs.Thms
import Init.Omega

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadFrame

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)

private def page : Page := ⟨⟨0⟩, 1, 2⟩
private def before : FileState := ⟨[10], some .readWrite, 0⟩
private def after : FileState := ⟨[10, 0, 99], some .readWrite, 0⟩

example : page.offset + page.size ≤ 2 ∧
    readBytes before.bytes page.offset page.size = readBytes after.bytes page.offset page.size ∧
    Trace.Valid (readWrite 8) before
      [⟨page.request, .shortRead [10, 0]⟩, ⟨.write page.handle 2 [99], .ok ()⟩,
        ⟨page.request, .ok [10, 0]⟩] after :=
  ⟨by decide, rfl, .cons rfl (.cons rfl (.cons rfl (.nil _)))⟩

example : ¬ AgreesOnPage before after page := by
  intro agrees
  have missing := agrees 1 (by decide)
  change none = some 0 at missing
  nomatch missing

private def shortPage : Page := ⟨⟨0⟩, 2, 2⟩
private def shortBefore : FileState := ⟨[11, 12, 13], some .readWrite, 0⟩
private def shortAfter : FileState := ⟨[99, 12, 13], some .readWrite, 0⟩

example : (readWrite 8 shortBefore shortPage.request).1 = .shortRead [13, 0] ∧
    (readWrite 8 shortBefore shortPage.request).1 = (readWrite 8 shortAfter shortPage.request).1 := by
  refine ⟨rfl, lawful_read_reply_agrees (readWrite_lawful 8).2.1 (readWrite_lawful 8).2.1
    shortBefore shortAfter shortPage (by decide) rfl rfl ?_⟩
  intro i inside
  change i < 2 at inside
  have index : i = 0 ∨ i = 1 := by omega
  rcases index with rfl | rfl <;> rfl

#print axioms read_result_agrees
#print axioms lawful_read_reply_agrees

end Silmaril.Machine.SqliteVfs.PageRead.ReadFrame
