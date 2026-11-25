module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.File.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.TableLeaf.Subview

open Silmaril.Formats Silmaril.Formats.Sqlite

private theorem materialize_length (view : File.View) : view.materialize.length = view.length := by
  have bounded : view.start + view.length ≤ view.source.data.size := view.bounded
  change (view.source.data.extract view.start (view.start + view.length)).size = view.length
  rw [ByteArray.size_extract, Nat.min_eq_left bounded, Nat.add_sub_cancel_left]

private theorem get?_materialize (view : File.View) (offset : Nat) :
    (File.View.ofBytes view.materialize).get? offset = view.get? offset := by
  by_cases inside : offset < view.length
  · have bounded : view.start + view.length ≤ view.source.data.size := view.bounded
    have backing : view.start + offset < view.source.data.size := by omega
    have extracted : offset < view.materialize.data.size := by
      change offset < view.materialize.length
      rwa [materialize_length]
    unfold File.View.get? File.View.ofBytes
    simp only [materialize_length, inside, ite_true, Nat.zero_add]
    rw [getElem?_pos view.materialize.data offset extracted,
        getElem?_pos view.source.data (view.start + offset) backing]
    exact congrArg some (ByteArray.getElem_extract extracted)
  · unfold File.View.get? File.View.ofBytes
    simp [materialize_length, inside]

private theorem readAux?_shift (copied parent : File.View) (base : Nat)
    (observed : ∀ i byte, copied.get? i = some byte → parent.get? (base + i) = some byte)
    (fuel offset acc value next : Nat)
    (parsed : Varint.readAux? copied fuel offset acc = some (value, next)) :
    Varint.readAux? parent fuel (base + offset) acc = some (value, base + next) := by
  induction fuel generalizing offset acc with
  | zero => simp [Varint.readAux?] at parsed
  | succ fuel ih =>
    cases fuel with
    | zero =>
      cases obtained : copied.get? offset with
      | none => simp [Varint.readAux?, obtained] at parsed
      | some byte =>
        rw [Varint.readAux?, obtained] at parsed
        change some (acc * 256 + byte.toNat, offset + 1) = _ at parsed
        simp only [Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨rfl, rfl⟩ := parsed
        rw [Varint.readAux?, observed offset byte obtained]
        change some (acc * 256 + byte.toNat, base + offset + 1) = _
        rw [Nat.add_assoc]
    | succ fuel =>
      cases obtained : copied.get? offset with
      | none => simp [Varint.readAux?, obtained] at parsed
      | some byte =>
        rw [Varint.readAux?, obtained] at parsed
        change (if byte.toNat < 128 then
            some (acc * 128 + byte.toNat % 128, offset + 1)
          else Varint.readAux? copied (fuel + 1) (offset + 1) (acc * 128 + byte.toNat % 128)) = _ at parsed
        rw [Varint.readAux?, observed offset byte obtained]
        change (if byte.toNat < 128 then
            some (acc * 128 + byte.toNat % 128, base + offset + 1)
          else Varint.readAux? parent (fuel + 1) (base + offset + 1) (acc * 128 + byte.toNat % 128)) = _
        by_cases terminal : byte.toNat < 128
        · simp only [ite_eq_left terminal, Option.some.injEq, Prod.mk.injEq] at parsed
          obtain ⟨rfl, rfl⟩ := parsed
          rw [ite_eq_left terminal, Nat.add_assoc]
        · rw [ite_eq_right terminal] at parsed
          rw [ite_eq_right terminal, Nat.add_assoc]
          exact ih (offset + 1) (acc * 128 + byte.toNat % 128) parsed

private theorem readNat?_shift (copied parent : File.View) (base : Nat)
    (observed : ∀ i byte, copied.get? i = some byte → parent.get? (base + i) = some byte)
    (offset value next : Nat)
    (parsed : Varint.readNat? copied offset = some (value, next)) :
    Varint.readNat? parent (base + offset) = some (value, base + next) :=
  readAux?_shift copied parent base observed 9 offset 0 value next parsed

private theorem read?_shift (copied parent : File.View) (base : Nat)
    (observed : ∀ i byte, copied.get? i = some byte → parent.get? (base + i) = some byte)
    (offset next : Nat) (value : UInt64)
    (parsed : Varint.read? copied offset = some (value, next)) :
    Varint.read? parent (base + offset) = some (value, base + next) := by
  unfold Varint.read? at parsed ⊢
  cases decoded : Varint.readNat? copied offset with
  | none => simp [decoded] at parsed
  | some pair =>
    obtain ⟨decodedValue, decodedNext⟩ := pair
    simp only [decoded, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨rfl, rfl⟩ := parsed
    rw [readNat?_shift copied parent base observed offset decodedValue decodedNext decoded]
    rfl

private theorem observe_subview (parent part : File.View) (base count : Nat)
    (sliced : parent.sub? base count = some part) :
    ∀ i byte, (File.View.ofBytes part.materialize).get? i = some byte →
      parent.get? (base + i) = some byte := by
  intro i byte seen
  rw [get?_materialize] at seen
  have within : i < count := by
    obtain ⟨_, _, length, _⟩ := File.View.sub?_spec parent part base count sliced
    by_contra outside
    have out : part.length ≤ i := by omega
    rw [File.View.get?_outOfBounds part i out] at seen
    cases seen
  rw [← File.View.sub?_read parent part base count i sliced within]
  exact seen

private theorem compose_subview (parent part payload : File.View) (base count offset size : Nat)
    (outer : parent.sub? base count = some part)
    (inner : (File.View.ofBytes part.materialize).sub? offset size = some payload) :
    ∃ direct, parent.sub? (base + offset) size = some direct ∧
      direct.materialize = payload.materialize := by
  obtain ⟨partSource, partStart, partLength, outerBound⟩ :=
    File.View.sub?_spec parent part base count outer
  obtain ⟨bodySource, bodyStart, bodyLength, innerBound⟩ :=
    File.View.sub?_spec (File.View.ofBytes part.materialize) payload offset size inner
  change payload.source = part.materialize at bodySource
  change payload.start = 0 + offset at bodyStart
  change offset + size ≤ part.materialize.length at innerBound
  rw [materialize_length, partLength] at innerBound
  have fits : base + offset + size ≤ parent.length := by omega
  let direct : File.View := ⟨parent.source, parent.start + (base + offset), size,
    by have := parent.bounded; omega⟩
  have directSlice : parent.sub? (base + offset) size = some direct := by
    simp [File.View.sub?, fits, direct]
  refine ⟨direct, directSlice, ?_⟩
  apply congrArg Bytes.mk
  change parent.source.data.extract (parent.start + (base + offset))
      (parent.start + (base + offset) + size) =
    payload.source.data.extract payload.start (payload.start + payload.length)
  rw [bodySource, bodyStart, bodyLength, Nat.zero_add]
  change _ = (part.source.data.extract part.start (part.start + part.length)).extract offset (offset + size)
  rw [ByteArray.extract_extract, Nat.min_eq_left (by omega :
    part.start + (offset + size) ≤ part.start + part.length), partSource, partStart]
  simp [Nat.add_assoc]

private theorem guard_then_some {α : Type} (condition : Prop) [Decidable condition]
    {body : Option α} {result : α} (found : (do guard condition; body) = some result) :
    condition ∧ body = some result := by
  by_cases check : condition
  · exact ⟨check, by simpa [guard, check] using found⟩
  · simp [guard, check] at found

theorem cell?_materialized_shift (parent part : File.View) (base count offset : Nat)
    (sliced : parent.sub? base count = some part) (cell : TableLeaf.Cell)
    (decoded : TableLeaf.cell? (File.View.ofBytes part.materialize) offset = some cell) :
    TableLeaf.cell? parent (base + offset) =
      some { cell with start := base + cell.start, stop := base + cell.stop } := by
  let copied := File.View.ofBytes part.materialize
  have observed := observe_subview parent part base count sliced
  change TableLeaf.cell? copied offset = some cell at decoded
  unfold TableLeaf.cell? at decoded
  change (Varint.readNat? copied offset).bind _ = some cell at decoded
  obtain ⟨⟨length, keyAt⟩, lengthRead, rest⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨capacity, rest⟩ := guard_then_some (length ≤ 477) rest
  obtain ⟨⟨key, payloadAt⟩, keyRead, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨payload, payloadRead, rest⟩ := Option.bind_eq_some_iff.mp rest
  let stop := max (payloadAt + length) (offset + 4)
  obtain ⟨localStop, rest⟩ := guard_then_some (stop ≤ copied.length) rest
  change some ⟨Int64.ofInt (File.signed 8 key.toNat), payload.materialize, offset, stop⟩ =
    some cell at rest
  have exactCell := Option.some.inj rest
  subst cell
  have parentLength := readNat?_shift copied parent base observed offset length keyAt lengthRead
  have parentKey := read?_shift copied parent base observed keyAt payloadAt key keyRead
  obtain ⟨direct, directRead, exactPayload⟩ :=
    compose_subview parent part payload base count payloadAt length sliced payloadRead
  obtain ⟨_, _, lengthEq, boundary⟩ := File.View.sub?_spec parent part base count sliced
  change stop ≤ part.materialize.length at localStop
  rw [materialize_length, lengthEq] at localStop
  have parentStop : base + stop ≤ parent.length := by omega
  have stopEq : max (base + payloadAt + length) (base + offset + 4) = base + stop := by
    simp [stop, Nat.add_assoc]
  simp [TableLeaf.cell?, parentLength, parentKey, directRead, exactPayload, guard, capacity,
    stopEq, parentStop]

end Silmaril.Proofs.Formats.Sqlite.TableLeaf.Subview
