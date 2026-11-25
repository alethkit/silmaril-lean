module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Presence.Thms
import Silmaril.Machine.SqliteVfs.Thms

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Presence
open Silmaril.Machine.SqliteVfs.PageRead.WriteExtent (presentCount)

private def page : Page := ⟨⟨0⟩, 1, 3⟩
private def before : FileState := ⟨[10], some .readOnly, 0⟩
private def after : FileState := ⟨[10, 0], some .readOnly, 0⟩

example :
    let fragments := readFragments (readOnly 8) page.handle before page.offset 1 [2]
    let whole := readFragments (readOnly 8) page.handle after page.offset 3 []
    fragments.reply = some (.shortRead [10, 0, 0]) ∧
      fragments.reply = whole.reply ∧
      presentCount before page = 1 ∧ presentCount after page = 2 :=
  by decide

example :
    let fragments := readFragments (readOnly 8) page.handle before page.offset 1 [2]
    let whole := readFragments (readOnly 8) page.handle after page.offset 3 []
    CacheHit.AgreesOnPage before after page ↔
      fragments.reply = whole.reply ∧ presentCount before page = presentCount after page :=
  fragment_reply_agreement_iff (readOnly_lawful 8).2.1 (readOnly_lawful 8).2.1 before after
    page (by decide) (by decide) (by decide) 1 3 [2] []
    (by decide) (by decide) (by simp) (by simp) rfl rfl

example : ¬ CacheHit.AgreesOnPage before after page := by
  intro agreement
  have absent := agreement 1 (by decide)
  change none = some 0 at absent
  nomatch absent

#print axioms fragment_reply_agreement_iff
