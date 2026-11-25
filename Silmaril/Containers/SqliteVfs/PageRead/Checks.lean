module

import Silmaril.Containers.SqliteVfs.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Thms

namespace Silmaril.Containers.SqliteVfs.PageRead

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def file : FileState := ⟨[10, 20, 30, 40, 50], some .readOnly, 0⟩
private def free : Cache
  | 0 | 1 => some .vacant
  | _ => none

private def second : Page := ⟨⟨0⟩, 2, 2⟩
private def third : Page := ⟨⟨0⟩, 3, 2⟩
private def backing : Handler FileState := readOnly 8

private def full : Outcome FileState := fill backing file free 0 second
private def short : Outcome FileState := fill backing full.file full.cache 1 third

example : full.result = .ok [30, 40] ∧
    full.cache 0 = some (.resident second [30, 40]) ∧ full.cache 1 = some .vacant :=
  ⟨rfl, rfl, rfl⟩

example : short.result = .error .shortRead ∧ short.cache 1 = some .vacant ∧
    short.trace = [⟨.read ⟨0⟩ 4 2, .shortRead [50, 0]⟩] :=
  ⟨rfl, rfl, rfl⟩

example : (runtime backing).beh file (.blocked (encode (full.trace ++ short.trace))) :=
  blocked_iff.mpr ⟨_, file, .cons rfl (.cons rfl (.nil _)), rfl⟩

example : (fill backing file full.cache 0 third).result = .error .unavailableSlot ∧
    (fill backing file full.cache 0 third).trace = [] :=
  ⟨rfl, rfl⟩

example : (fill backing file free 2 third).result = .error .unavailableSlot ∧
    (fill backing file free 2 third).trace = [] :=
  ⟨rfl, rfl⟩

example : (fill backing file free 0 {second with number := 0}).result = .error .invalidPage ∧
    (fill backing file free 0 {second with number := 0}).trace = [] :=
  ⟨rfl, rfl⟩

private def malformed : Handler FileState :=
  fun state request => match request with
  | .read .. => (.ok [1], {state with generation := state.generation + 1})
  | operation => backing state operation

private def rejected : Outcome FileState := fill malformed file free 0 second

example : rejected.result = .error .wrongLength ∧ rejected.cache 0 = some .vacant ∧
    rejected.trace = [⟨.read ⟨0⟩ 2 2, .ok [1]⟩] ∧ rejected.file.generation = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms fill_trace
#print axioms fill_other
#print axioms fill_rejected
#print axioms fill_success
#print axioms readOnly_fill

end Silmaril.Containers.SqliteVfs.PageRead
