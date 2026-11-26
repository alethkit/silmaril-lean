module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Chunks.Concat

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit (combine)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (readFragments)

/-- Two nonempty ordered chunks use the same exchanges, actual endpoint and
aggregate reply as their concatenated fragment schedule. -/
theorem read_fragments_chunks {State : Type} (handler : Handler State)
    (handle : Handle) (start : State) (offset firstCount : Nat) (firstRest : List Nat)
    (secondCount : Nat) (secondRest : List Nat) :
    let first := readFragments handler handle start offset firstCount firstRest
    let second := readFragments handler handle first.file (offset + firstCount + firstRest.sum)
      secondCount secondRest
    let together := readFragments handler handle start offset firstCount
      (firstRest ++ (secondCount :: secondRest))
    together.file = second.file ∧ together.trace = first.trace ++ second.trace ∧
      together.reply = first.reply.bind (fun reply => second.reply.bind (combine reply)) :=
  Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Chunks.read_fragments_chunks
    handler handle start offset firstCount firstRest secondCount secondRest

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Chunks
