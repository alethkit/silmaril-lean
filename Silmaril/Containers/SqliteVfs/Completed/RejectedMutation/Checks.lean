module

import Silmaril.Containers.SqliteVfs.Completed.RejectedMutation.Thms
import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.Thms

namespace Silmaril.Containers.SqliteVfs.Completed.RejectedMutation

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.Completed
open Silmaril.Machine.SqliteVfs

private def start : FileState := ⟨[10, 20, 30, 40], some .readWrite, 0⟩
private def finish : FileState := ⟨[10, 20], some .readWrite, 0⟩
private def read : Request := .read ⟨0⟩ 0 2
private def refused : Exchange := ⟨.write ⟨0⟩ 4 [99], .error .full⟩
private def retained : Exchange := ⟨.truncate ⟨0⟩ 2, .ok ()⟩

private theorem valid : Trace.Valid (readWrite 4) start [refused, retained] finish :=
  .cons (show readWrite 4 start refused.request = (refused.response, start) from rfl)
    (.cons (show readWrite 4 start retained.request = (retained.response, finish) from rfl)
      (.nil _))

example : (machine (readWrite 4)).Exec Mach.seqPolicy (.idle start)
    (encode [retained]) (.idle finish) ∧ completed (encode [retained]) = [retained] := by
  have observed : (machine (readWrite 4)).Exec Mach.seqPolicy (.idle start)
      (encode [refused, retained]) (.idle finish) :=
    exec_iff.mpr ⟨_, finish, valid, .inl ⟨rfl, rfl⟩⟩
  exact execution_without_rejected_mutations (readWrite_lawful 4).2.2 observed

example : (machine (readWrite 4)).Exec Mach.seqPolicy (.idle start)
    (encode [retained] ++ [.recv read]) (.pending finish read) ∧
    completed (encode [retained] ++ [.recv read]) = [retained] := by
  have observed : (machine (readWrite 4)).Exec Mach.seqPolicy (.idle start)
      (encode [refused, retained] ++ [.recv read]) (.pending finish read) :=
    exec_iff.mpr ⟨_, finish, valid, .inr ⟨read, rfl, rfl⟩⟩
  exact execution_without_rejected_mutations (readWrite_lawful 4).2.2 observed

#print axioms execution_without_rejected_mutations

end Silmaril.Containers.SqliteVfs.Completed.RejectedMutation
