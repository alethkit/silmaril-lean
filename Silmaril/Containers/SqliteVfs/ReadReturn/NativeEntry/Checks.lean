module

import Silmaril.Containers.SqliteVfs.ReadReturn.NativeEntry.Thms
import Silmaril.Machine.SqliteRead.Thms
import Init.Omega

namespace Silmaril.Containers.SqliteVfs.ReadReturn.NativeEntry

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.ReadEntry (projectEntry)
open Silmaril.Containers.SqliteVfs.ReadReturn (projectReturn)
open Silmaril.Elf.Corpus.SqliteRead (Dispatches argument observe run)
open Silmaril.Machine
open Silmaril.Machine.Behaviour.Observable (Safe)
open Silmaril.Machine.SqliteRead (BufferView Status)
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary
open Silmaril.X86 (MState Word)
open Silmaril.X86.Ext.Wire (Platform)

private def elfPage : Silmaril.Elf.Corpus.SqliteRead.PageRead := ⟨16, 32, 2, 1⟩
private def page : Page := ⟨⟨0⟩, 2, 2⟩
private def file : FileState := ⟨[11, 22, 33], some .readOnly, 0⟩
private def cache : Cache := fun _ => some .vacant
private def env : SqliteRead.Context := ⟨fun _ => True, fun _ _ => True⟩
private def binding : FileBinding := fun address => if address = 16 then some ⟨0⟩ else none
private def before : BufferView := fun _ => none
private def after : BufferView :=
  fun address => if address = 32 then some 33 else if address = 33 then some 0 else none
private def exchange : Exchange := ⟨page.request, .shortRead [33, 0]⟩

private theorem safe : Safe ((SqliteRead.contract env).spec elfPage.request) :=
  (SqliteRead.safe_iff_admitted env elfPage.request).mpr
    ⟨by decide, trivial, by decide, by decide, by decide, by decide, by decide, trivial⟩

private theorem handlerLaw :
    SqliteRead.Handler (file.bytes.map UInt8.toBitVec) elfPage.request before after .shortRead := by
  refine ⟨?_, by decide, ?_⟩
  · intro address outside
    change address < 32 ∨ 34 ≤ address at outside
    simp [before, after, show address ≠ 32 from by omega, show address ≠ 33 from by omega]
  · intro index within
    change index < 2 at within
    have position : index = 0 ∨ index = 1 := by omega
    rcases position with rfl | rfl <;> rfl

example {platform : Platform} {initial : MState} {methods target : Word}
    (entry : Silmaril.Elf.Corpus.SqliteRead.Entry initial elfPage methods target) :
    ∃ reached, Dispatches platform initial elfPage.request target reached ∧
      projectReturn binding (argument reached.core) after .shortRead = some exchange ∧
      (machine (readOnly 8)).Exec Mach.seqPolicy (.idle file) (encode [exchange]) (.idle file) := by
  obtain ⟨reached, actual, dispatched, _, returned, _, trace, execution⟩ :=
    pinned_entry_with_modeled_return 8 file cache 0 (platform := platform) (binding := binding)
      page entry safe rfl rfl rfl rfl rfl before after .shortRead handlerLaw (.inr rfl)
  have exactTrace : (fill (readOnly 8) file cache 0 page).trace = [exchange] := rfl
  have same : actual = exchange := (List.cons.inj (trace.symm.trans exactTrace)).1
  subst actual
  exact ⟨reached, dispatched, returned, execution⟩

#print axioms pinned_entry_with_modeled_return

end Silmaril.Containers.SqliteVfs.ReadReturn.NativeEntry
