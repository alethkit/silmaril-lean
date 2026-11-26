module

import Silmaril.Containers.SqliteVfs.FragmentPrefix.Thms

namespace Silmaril.Containers.SqliteVfs.FragmentPrefix

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)

private def handle : Handle := ⟨0⟩
private def initial : FileState := ⟨[13], some .readOnly, 0⟩

private def counted : Handler (FileState × Nat) := fun state request =>
  let (reply, next) := readOnly 8 state.1 request
  (reply, next, state.2 + 1)

private def zeroRead : Request := .read handle 0 0
private def oneRead : Request := .read handle 0 1
private def nextRead : Request := .read handle 1 1
private def history : List Event :=
  encode [⟨zeroRead, .error .invalidRange⟩, ⟨oneRead, .ok [13]⟩]

example :
    (machine counted).Exec Mach.seqPolicy (.idle (initial, 5)) history (.idle (initial, 7)) ∧
      (completed history).map Exchange.request = fragmentRequests handle 0 [0, 1] :=
  (exec_fragment_prefix_iff counted handle (initial, 5) 0 0 [1] history (.idle (initial, 7))).mpr
    (.inl ⟨rfl, rfl⟩)

example :
    let events := history ++ [.recv nextRead]
    (machine counted).Exec Mach.seqPolicy (.idle (initial, 5)) events (.pending (initial, 7) nextRead) ∧
      (completed events).map Exchange.request = fragmentRequests handle 0 [0, 1] :=
  (exec_fragment_prefix_iff counted handle (initial, 5) 0 0 [1] (history ++ [.recv nextRead])
    (.pending (initial, 7) nextRead)).mpr (.inr ⟨nextRead, rfl, rfl⟩)

example :
    ¬ (machine counted).Exec Mach.seqPolicy (.idle (initial, 5))
        (history ++ [.recv nextRead]) (.pending (initial, 8) nextRead) := by
  intro execution
  have shape :=
    (exec_fragment_prefix_iff counted handle (initial, 5) 0 0 [1] (history ++ [.recv nextRead])
      (.pending (initial, 8) nextRead)).mp ⟨execution, rfl⟩
  rcases shape with ⟨_, phase⟩ | ⟨_, _, phase⟩ <;> cases phase

end Silmaril.Containers.SqliteVfs.FragmentPrefix
