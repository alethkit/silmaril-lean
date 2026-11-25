module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Containers.SqliteVfs.Completed.Thms
import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Thms

@[expose] public section

namespace Silmaril.Proofs.Containers.SqliteVfs.FragmentReads

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments

/-- Both read schedules are observations of the public serial container.
The result and final file view agree after reassembly. Each observation
retains its own request and reply events and actual idle endpoint. -/
theorem read_observations {State : Type} {handler : Handler State} {view : State → FileState}
    (law : ReadLaw handler view) (start : State) (handle : Handle) (offset count : Nat)
    (rest : List Nat) (countPositive : 0 < count) (restPositive : ∀ n ∈ rest, 0 < n)
    (admitted : ReadRange offset (count + rest.sum : Nat))
    (live : ((view start).mode handle).isNone = false) :
    let fragmented := readFragments handler handle start offset count rest
    let request := Request.read handle offset (count + rest.sum : Nat)
    let whole := handler start request
    let one : Trace := [⟨request, whole.1⟩]
    let fragmentEvents := encode fragmented.trace
    let wholeEvents := encode one
    fragmented.reply = some whole.1 ∧ view fragmented.file = view whole.2 ∧
      (machine handler).Exec Mach.seqPolicy (.idle start) fragmentEvents (.idle fragmented.file) ∧
      (machine handler).Exec Mach.seqPolicy (.idle start) wholeEvents (.idle whole.2) ∧
      (runtime handler).beh start (.blocked fragmentEvents) ∧
      (runtime handler).beh start (.blocked wholeEvents) ∧
      Silmaril.Containers.SqliteVfs.Completed.completed fragmentEvents = fragmented.trace ∧
      Silmaril.Containers.SqliteVfs.Completed.completed wholeEvents = one := by
  dsimp only
  obtain ⟨reply, sameView, fragmentValid, _, wholeValid⟩ :=
    read_fragments_sound law start handle offset count rest countPositive restPositive admitted live
  have execute {trace : Trace} {finish : State} (valid : Trace.Valid handler start trace finish) :
      (machine handler).Exec Mach.seqPolicy (.idle start) (encode trace) (.idle finish) :=
    Silmaril.Containers.SqliteVfs.exec_iff.mpr ⟨trace, finish, valid, Or.inl ⟨rfl, rfl⟩⟩
  have blocked {trace : Trace} {finish : State} (valid : Trace.Valid handler start trace finish) :
      (runtime handler).beh start (.blocked (encode trace)) :=
    Silmaril.Containers.SqliteVfs.blocked_iff.mpr ⟨trace, finish, valid, rfl⟩
  exact ⟨reply, sameView, execute fragmentValid, execute wholeValid,
    blocked fragmentValid, blocked wholeValid, Silmaril.Containers.SqliteVfs.Completed.completed_encode _,
    Silmaril.Containers.SqliteVfs.Completed.completed_encode _⟩

end Silmaril.Proofs.Containers.SqliteVfs.FragmentReads
