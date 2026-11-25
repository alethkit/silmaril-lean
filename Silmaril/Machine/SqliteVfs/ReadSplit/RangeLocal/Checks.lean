module

import Silmaril.Machine.SqliteVfs.ReadSplit.RangeLocal.Thms
import Init.Omega

namespace Silmaril.Machine.SqliteVfs.ReadSplit.RangeLocal

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit (combine)

private def token : Handle := ⟨0⟩

private def start (tail : Bytes) : FileState := ⟨1 :: 10 :: tail, some .readOnly, 0⟩

private def changesPrefix : Handler FileState := fun state req =>
  match req with
  | .read handle offset count =>
    let (reply, after) := readOnly 8 state (.read handle offset count)
    if offset = 1 ∧ count = 1 then (reply, { after with bytes := 90 :: after.bytes.drop 1 })
    else (reply, after)
  | other => readOnly 8 state other

private theorem readBacking_result (bytes : Bytes) (offset count : Nat) :
    ReadResult bytes offset count (readBacking bytes offset count) := by
  refine ⟨readBytes bytes offset count, rfl, by simp [readBytes], ?_⟩
  intro i inside
  simp [readBytes, inside]

private theorem fixture (tail : Bytes) :
    let initial := start tail
    let firstReq := Request.read token 1 1
    let secondReq := Request.read token 2 1
    let wholeReq := Request.read token 1 2
    let first := changesPrefix initial firstReq
    let second := changesPrefix first.2 secondReq
    let whole := changesPrefix initial wholeReq
    combine first.1 second.1 = some whole.1 ∧
      second.2.bytes ≠ whole.2.bytes ∧
      Trace.Valid changesPrefix initial [⟨firstReq, first.1⟩, ⟨secondReq, second.1⟩] second.2 ∧
      Trace.Valid changesPrefix initial [⟨wholeReq, whole.1⟩] whole.2 := by
  have agree := reads_split_of_suffix_agreement changesPrefix id (start tail) token 1 1 1 (by decide)
    (by
      intro i inside
      have : i = 0 := by omega
      subst i
      rfl)
    (readBacking_result (1 :: 10 :: tail) 1 1)
    (readBacking_result (90 :: 10 :: tail) 2 1)
    (readBacking_result (1 :: 10 :: tail) 1 2)
  refine ⟨agree.1, ?_, agree.2⟩
  intro same
  have head := congrArg List.head? same
  exact (by decide : (some (90 : UInt8)) ≠ some 1) head

example :
    let initial := start [20]
    let first := changesPrefix initial (.read token 1 1)
    let second := changesPrefix first.2 (.read token 2 1)
    let whole := changesPrefix initial (.read token 1 2)
    combine first.1 second.1 = some whole.1 ∧ whole.1 = .ok [10, 20] ∧
      second.2.bytes = [90, 10, 20] ∧ whole.2.bytes = [1, 10, 20] :=
  ⟨(fixture [20]).1, rfl, rfl, rfl⟩

example :
    let initial := start []
    let first := changesPrefix initial (.read token 1 1)
    let second := changesPrefix first.2 (.read token 2 1)
    let whole := changesPrefix initial (.read token 1 2)
    combine first.1 second.1 = some whole.1 ∧ whole.1 = .shortRead [10, 0] ∧
      second.2.bytes = [90, 10] ∧ whole.2.bytes = [1, 10] :=
  ⟨(fixture []).1, rfl, rfl, rfl⟩

example :
    let initial := start []
    let first := changesPrefix initial (.read token 1 1)
    ReadRange 1 1 ∧ ReadRange 2 1 ∧ ReadRange 1 2 ∧
      (initial.mode token).isNone = false ∧ (first.2.mode token).isNone = false := by decide

private def growsAtEof : Handler FileState := fun state req =>
  match req with
  | .read handle offset count =>
    let (reply, after) := readOnly 8 state (.read handle offset count)
    if offset = 1 ∧ count = 1 then (reply, { after with bytes := after.bytes ++ [0] })
    else (reply, after)
  | other => readOnly 8 state other

example :
    let initial := start []
    let first := growsAtEof initial (.read token 1 1)
    let second := growsAtEof first.2 (.read token 2 1)
    let whole := growsAtEof initial (.read token 1 2)
    initial.bytes[2]? ≠ first.2.bytes[2]? ∧
      combine first.1 second.1 = some (.ok [10, 0]) ∧ whole.1 = .shortRead [10, 0] :=
  ⟨by decide, rfl, rfl⟩

end Silmaril.Machine.SqliteVfs.ReadSplit.RangeLocal
