module

import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks.Thms

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks

open Silmaril.Machine.SqliteVfs

private def handle : Handle := ⟨0⟩
private def initial : FileState := ⟨[7, 8, 9], some .readOnly, 0⟩
private def counted : Handler (FileState × Nat) := fun state request =>
  let (reply, next) := readOnly 8 state.1 request
  (reply, next, state.2 + 1)

example :
    let first := readFragments counted handle (initial, 5) 1 1 [1]
    let second := readFragments counted handle first.file 3 1 [1]
    let together := readFragments counted handle (initial, 5) 1 1 [1, 1, 1]
    first.file = (initial, 7) ∧ together.file = (initial, 9) ∧
      together.trace = first.trace ++ second.trace ∧
      together.reply = some (.shortRead [8, 9, 0, 0]) :=
  ⟨rfl, rfl, (read_fragments_chunks counted handle (initial, 5) 1 1 [1] 1 [1]).2.1, rfl⟩

example :
    let first := readFragments counted handle (initial, 5) 0 0 [1]
    let second := readFragments counted handle first.file 1 1 []
    let together := readFragments counted handle (initial, 5) 0 0 [1, 1]
    first.trace = [⟨.read handle 0 0, .error .invalidRange⟩, ⟨.read handle 0 1, .ok [7]⟩] ∧
      second.trace = [⟨.read handle 1 1, .ok [8]⟩] ∧
      together.trace = first.trace ++ second.trace ∧
      together.file = (initial, 8) ∧ together.reply = none :=
  ⟨rfl, rfl, (read_fragments_chunks counted handle (initial, 5) 0 0 [1] 1 []).2.1, rfl, rfl⟩

private def changesBytes : Handler FileState := fun state request =>
  let (reply, next) := readOnly 8 state request
  (reply, { next with bytes := [17, 42] })

example :
    let first := readFragments changesBytes handle initial 0 1 []
    let second := readFragments changesBytes handle first.file 1 1 []
    let together := readFragments changesBytes handle initial 0 1 [1]
    second.trace = [⟨.read handle 1 1, .ok [42]⟩] ∧
      together.file = second.file ∧ together.reply = some (.ok [7, 42]) :=
  ⟨rfl, (read_fragments_chunks changesBytes handle initial 0 1 [] 1 []).1, rfl⟩

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks
