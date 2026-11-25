module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.File.Thms
import Silmaril.Formats.Sqlite.Varint.Thms

public section
namespace Silmaril.Proofs.Formats.Sqlite.TableLeaf

open Silmaril.Formats Silmaril.Formats.Sqlite Silmaril.Formats.Sqlite.TableLeaf

/-- A successful varint read only inspects the bytes before its returned cursor. -/
private theorem readAuxFrame (left right : File.View) (fuel offset acc value next : Nat)
    (read : Varint.readAux? left fuel offset acc = some (value, next))
    (same : ∀ i, offset ≤ i → i < next → left.get? i = right.get? i) :
    Varint.readAux? right fuel offset acc = some (value, next) := by
  induction fuel generalizing offset acc with
  | zero => simp [Varint.readAux?] at read
  | succ fuel ih =>
    have first := same offset (Nat.le_refl _) (Varint.readAux?_progress _ _ _ _ _ _ read).1
    cases fuel with
    | zero => simpa only [Varint.readAux?, ← first] using read
    | succ fuel =>
      rw [Varint.readAux?] at read ⊢
      cases byte : left.get? offset with
      | none => simp [byte] at read
      | some b =>
        have other := first.symm.trans byte
        simp [byte, other] at read ⊢
        by_cases terminal : b.toNat < 128
        · simpa only [terminal, ite_true] using read
        · simp only [terminal, ite_false] at read ⊢
          exact ih _ _ read (fun i after before => same i (by omega) before)

private theorem readKeyFrame (left right : File.View) (offset next : Nat) (key : UInt64)
    (read : Varint.read? left offset = some (key, next))
    (same : ∀ i, offset ≤ i → i < next → left.get? i = right.get? i) :
    Varint.read? right offset = some (key, next) := by
  unfold Varint.read? at read ⊢
  cases raw : Varint.readNat? left offset with
  | none => simp [raw] at read
  | some result =>
    obtain ⟨value, stop⟩ := result
    simp only [raw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    have other : Varint.readNat? right offset = some (value, stop) :=
      readAuxFrame left right 9 offset 0 value stop raw same
    rw [other]
    rfl

private theorem materializeEq (left right : File.View) (length : left.length = right.length)
    (same : ∀ i, i < left.length → left.get? i = right.get? i) :
    left.materialize = right.materialize := by
  have leftBound : left.start + left.length ≤ left.source.data.size := left.bounded
  have rightBound : right.start + right.length ≤ right.source.data.size := right.bounded
  unfold File.View.materialize
  apply congrArg Bytes.mk
  apply ByteArray.ext_getElem
  · simp only [ByteArray.size_extract]
    omega
  · intro i leftInside rightInside
    have inside : i < left.length := by
      rw [ByteArray.size_extract] at leftInside
      omega
    have otherInside : i < right.length := length ▸ inside
    have leftIndex : left.start + i < left.source.data.size := by omega
    have rightIndex : right.start + i < right.source.data.size := by omega
    have equal := same i inside
    simp only [File.View.get?, inside, otherInside, ↓reduceIte, getElem?_pos, leftIndex,
      rightIndex, Option.some.injEq] at equal
    simpa only [ByteArray.getElem_extract] using equal

theorem cell?_frame (left right : File.View) (start : Nat) (cell : Cell)
    (parsed : cell? left start = some cell) (fits : cell.stop ≤ right.length)
    (same : ∀ i, start ≤ i → i < cell.stop → left.get? i = right.get? i) :
    cell? right start = some cell := by
  cases lengthRead : Varint.readNat? left start with
  | none => simp [cell?, guard, failure, lengthRead] at parsed
  | some lengthResult =>
    obtain ⟨size, keyAt⟩ := lengthResult
    by_cases localPayload : size ≤ 477
    · cases keyRead : Varint.read? left keyAt with
      | none => simp [cell?, guard, failure, lengthRead, localPayload, keyRead] at parsed
      | some keyResult =>
        obtain ⟨key, payloadAt⟩ := keyResult
        cases payloadRead : left.sub? payloadAt size with
        | none => simp [cell?, guard, failure, lengthRead, localPayload, keyRead, payloadRead] at parsed
        | some payload =>
          by_cases leftFits : max (payloadAt + size) (start + 4) ≤ left.length
          · simp [cell?, guard, failure, lengthRead, localPayload, keyRead, payloadRead, leftFits] at parsed
            subst cell
            have keyProgress := (Varint.read?_progress _ _ _ _ keyRead).1
            have lengthProgress := (Varint.readAux?_progress left 9 start 0 size keyAt lengthRead).1
            have rightLength : Varint.readNat? right start = some (size, keyAt) :=
              readAuxFrame left right 9 start 0 size keyAt lengthRead
                (fun i after before => same i after (by dsimp; omega))
            have rightKey := readKeyFrame left right keyAt payloadAt key keyRead
              (fun i after before => same i (by omega) (by dsimp; omega))
            have endFits : payloadAt + size ≤ right.length := by dsimp at fits; omega
            let other : File.View := ⟨right.source, right.start + payloadAt, size, by
              have := right.bounded
              omega⟩
            have rightPayload : right.sub? payloadAt size = some other := by
              simp [File.View.sub?, endFits, other]
            have sizeEq := (File.View.sub?_spec left payload payloadAt size payloadRead).2.2.1
            have payloadEq : payload.materialize = other.materialize := by
              apply materializeEq payload other sizeEq
              intro i inside
              have hi : i < size := sizeEq ▸ inside
              rw [File.View.sub?_read left payload _ _ _ payloadRead hi,
                File.View.sub?_read right other _ _ _ rightPayload hi]
              exact same _ (by omega) (by dsimp; omega)
            dsimp at fits
            simp [cell?, guard, failure, rightLength, localPayload, rightKey, rightPayload, fits, payloadEq]
          · simp [cell?, guard, failure, lengthRead, localPayload, keyRead, payloadRead, leftFits] at parsed
    · simp [cell?, guard, failure, lengthRead, localPayload] at parsed

end Silmaril.Proofs.Formats.Sqlite.TableLeaf
