module

import Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation.Thms
import Silmaril.Machine.SqliteVfs.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.MutationTrace

private def start : FileState := ⟨[10, 20, 30, 40], some .readWrite, 0⟩
private def finish : FileState := ⟨[10, 20], some .readWrite, 0⟩
private def refusedWrite : Exchange := ⟨.write ⟨0⟩ 4 [90], .error .full⟩
private def refusedTruncate : Exchange := ⟨.truncate ⟨1⟩ 0, .error .invalidHandle⟩
private def retainedTruncate : Exchange := ⟨.truncate ⟨0⟩ 2, .ok ()⟩

private theorem fixture :
    Trace.Valid (readWrite 4) start [refusedWrite, refusedTruncate, retainedTruncate] finish :=
  .cons (show readWrite 4 start refusedWrite.request = (refusedWrite.response, start) from rfl)
    (.cons (show readWrite 4 start refusedTruncate.request = (refusedTruncate.response, start) from rfl)
      (.cons (show readWrite 4 start retainedTruncate.request = (retainedTruncate.response, finish) from rfl)
        (.nil _)))

example : Trace.Valid (readWrite 4) start [retainedTruncate] finish :=
  erase_rejected_mutations (readWrite_lawful 4).2.2 fixture

private def page : Page := ⟨⟨0⟩, 1, 2⟩

example : CacheHit.AgreesOnPage start finish page ∧
    finish.mode page.handle = start.mode page.handle := by
  refine retains_with_rejections page fixture ?_ (by decide) (by decide)
  intro exchange member
  change exchange ∈ [retainedTruncate] at member
  have exactExchange := List.mem_singleton.mp member
  subst exchange
  exact .truncate 2 (by decide)

#print axioms erase_rejected_mutations
#print axioms retains_with_rejections

end Silmaril.Machine.SqliteVfs.PageRead.RejectedMutation
