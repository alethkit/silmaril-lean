module

import Silmaril.Containers.SqliteVfs.FragmentResume.Thms
import Silmaril.Containers.SqliteVfs.FragmentPrefix.Thms

namespace Silmaril.Containers.SqliteVfs.FragmentResume

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs.FragmentPrefix (exec_fragment_prefix_iff)

private def handle : Handle := ⟨0⟩
private def initial : FileState := ⟨[7], some .readOnly, 0⟩
private def counted : Handler (FileState × Nat) := fun state request =>
  let (reply, next) := readOnly 8 state.1 request
  (reply, next, state.2 + 1)
private def first : Exchange := ⟨.read handle 0 1, .ok [7]⟩
private def bad : Request := .read handle 1 0
private def badEvents : List Event := encode [first] ++ [.recv bad]

example :
    let after := readFragments counted handle (initial, 5) 0 1 [0]
    (machine counted).Exec Mach.seqPolicy (.idle (initial, 5))
      (badEvents ++ [.send ⟨bad, .error .invalidRange⟩]) (.idle (initial, 7)) ∧
      completed (badEvents ++ [.send ⟨bad, .error .invalidRange⟩]) = after.trace ∧
      after.reply = none := by
  have pending : (machine counted).Exec Mach.seqPolicy (.idle (initial, 5))
      badEvents (.pending (initial, 6) bad) :=
    ((exec_fragment_prefix_iff counted handle (initial, 5) 0 1 [] badEvents
      (.pending (initial, 6) bad)).mpr (.inr ⟨bad, rfl, rfl⟩)).1
  obtain ⟨_, _, _, _, resumed, trace⟩ :=
    complete_pending_fragment counted handle (initial, 5) 0 1 [] 0 badEvents pending rfl
  exact ⟨resumed, trace, rfl⟩

private def beyond : Request := .read handle 1 2
private def eofEvents : List Event := encode [first] ++ [.recv beyond]

example :
    let after := readFragments counted handle (initial, 5) 0 1 [2]
    (machine counted).Exec Mach.seqPolicy (.idle (initial, 5))
      (eofEvents ++ [.send ⟨beyond, .shortRead [0, 0]⟩]) (.idle (initial, 7)) ∧
      after.reply = some (.shortRead [7, 0, 0]) := by
  have pending : (machine counted).Exec Mach.seqPolicy (.idle (initial, 5))
      eofEvents (.pending (initial, 6) beyond) :=
    ((exec_fragment_prefix_iff counted handle (initial, 5) 0 1 [] eofEvents
      (.pending (initial, 6) beyond)).mpr (.inr ⟨beyond, rfl, rfl⟩)).1
  obtain ⟨_, _, _, _, resumed, _⟩ :=
    complete_pending_fragment counted handle (initial, 5) 0 1 [] 2 eofEvents pending rfl
  exact ⟨resumed, rfl⟩

end Silmaril.Containers.SqliteVfs.FragmentResume
