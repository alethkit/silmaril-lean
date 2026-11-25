module

import Silmaril.Containers.SqliteVfs.FragmentReads.Thms
import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Thms
import Silmaril.Machine.SqliteVfs.Thms

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.FragmentReads
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments

private def file : FileState := ⟨[11, 22, 33, 44, 0, 77], some .readOnly, 0⟩
private def handle : Handle := ⟨0⟩

private def counted : Handler (FileState × Nat) :=
  fun state req =>
    let result := readOnly 8 state.1 req
    (result.1, result.2, state.2 + 1)

private theorem counted_law : ReadLaw counted Prod.fst where
  read state := (readOnly_lawful 8).2.1.read state.1
  fileSize state := (readOnly_lawful 8).2.1.fileSize state.1

example :
    let fragmented := readFragments counted handle (file, 0) 3 2 [1, 1]
    let whole := counted (file, 0) (.read handle 3 4)
    fragmented.reply = some (.shortRead [44, 0, 77, 0]) ∧
      fragmented.file = (file, 3) ∧ whole.2 = (file, 1) ∧
      (encode fragmented.trace).length = 6 ∧
      (encode [⟨.read handle 3 4, whole.1⟩]).length = 2 := by decide

example :
    let fragmented := readFragments counted handle (file, 0) 3 2 [1, 1]
    let request := Request.read handle 3 4
    let whole := counted (file, 0) request
    fragmented.reply = some whole.1 ∧ fragmented.file.1 = whole.2.1 ∧
      (machine counted).Exec Mach.seqPolicy (.idle (file, 0)) (encode fragmented.trace) (.idle fragmented.file) ∧
      (machine counted).Exec Mach.seqPolicy (.idle (file, 0)) (encode [⟨request, whole.1⟩]) (.idle whole.2) ∧
      (runtime counted).beh (file, 0) (.blocked (encode fragmented.trace)) ∧
      (runtime counted).beh (file, 0) (.blocked (encode [⟨request, whole.1⟩])) ∧
      Completed.completed (encode fragmented.trace) = fragmented.trace ∧
      Completed.completed (encode [⟨request, whole.1⟩]) = [⟨request, whole.1⟩] :=
  read_observations counted_law (file, 0) handle 3 2 [1, 1]
    (by decide) (by simp) (by decide) (by decide)

private def zeroCountTrace : Trace :=
  [⟨.read handle 0 1, .ok [11]⟩, ⟨.read handle 1 0, .error .invalidRange⟩,
   ⟨.read handle 1 2, .ok [22, 33]⟩]

example :
    (runtime counted).beh (file, 0) (.blocked (encode zeroCountTrace)) := by
  apply blocked_iff.mpr
  exact ⟨zeroCountTrace, (file, 3),
    (read_fragments_trace counted handle (file, 0) 0 1 [0, 2]).1, rfl⟩

#print axioms read_observations
#print axioms counted_law
