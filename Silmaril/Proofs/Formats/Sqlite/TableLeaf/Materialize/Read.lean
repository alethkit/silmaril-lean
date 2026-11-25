module

public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Formats.Sqlite.File.Thms
import Silmaril.Formats.Sqlite.File.View.Materialize.Thms

public section

namespace Silmaril.Proofs.Formats.Sqlite.TableLeaf.Materialize

open Silmaril.Formats.Sqlite.File (View)
open Silmaril.Formats.Sqlite

/-- Page-local observations used by the packed leaf parser. -/
private structure Same (a b : View) : Prop where
  length : a.length = b.length
  get (i : Nat) : a.get? i = b.get? i

private theorem same_copy (view : View) : Same view (View.ofBytes view.materialize) := by
  have length : (View.ofBytes view.materialize).length = view.length := View.materialize_length view
  refine ⟨length.symm, fun i => ?_⟩
  by_cases inside : i < view.length
  · have hcopy : i < (View.ofBytes view.materialize).length := length ▸ inside
    rw [← View.materialize_get? view i inside]
    unfold View.get?
    rw [ite_eq_left hcopy]
    simp only [View.ofBytes]
    rw [Silmaril.Formats.Bytes.toList, Array.getElem?_toList]
    have bound : i < view.materialize.data.size := hcopy
    rw [Nat.zero_add, Array.getElem?_eq_getElem (show i < view.materialize.data.data.size from bound),
      getElem?_pos view.materialize.data i bound]
    rfl
  · rw [View.get?_outOfBounds view i (Nat.le_of_not_lt inside),
      View.get?_outOfBounds _ _ (length ▸ Nat.le_of_not_lt inside)]

private theorem Same.materialize {a b : View} (same : Same a b) :
    a.materialize = b.materialize := by
  apply Silmaril.Formats.Bytes.ext
  apply List.ext_getElem?
  intro i
  by_cases inside : i < a.length
  · rw [View.materialize_get? a i inside, View.materialize_get? b i (same.length ▸ inside), same.get]
  · have outside := Nat.le_of_not_lt inside
    rw [List.getElem?_eq_none (by simpa [View.materialize_length] using outside),
      List.getElem?_eq_none (by simpa [View.materialize_length, ← same.length] using outside)]

private theorem Same.slice {a b : View} (same : Same a b) (offset count : Nat) :
    (a.sub? offset count).map View.materialize = (b.sub? offset count).map View.materialize := by
  by_cases fits : offset + count ≤ a.length
  · have fitsB : offset + count ≤ b.length := same.length ▸ fits
    have aSub : ∃ part, a.sub? offset count = some part := by
      simp [View.sub?, fits]
    have bSub : ∃ part, b.sub? offset count = some part := by
      simp [View.sub?, fitsB]
    obtain ⟨ap, ha⟩ := aSub
    obtain ⟨bp, hb⟩ := bSub
    simp only [ha, hb, Option.map_some, Option.some.injEq]
    have aLen := (View.sub?_spec a ap offset count ha).2.2.1
    have bLen := (View.sub?_spec b bp offset count hb).2.2.1
    apply Same.materialize
    refine ⟨aLen.trans bLen.symm, fun i => ?_⟩
    by_cases inside : i < count
    · rw [View.sub?_read a ap offset count i ha inside, View.sub?_read b bp offset count i hb inside,
        same.get]
    · rw [View.get?_outOfBounds ap i (aLen ▸ Nat.le_of_not_lt inside),
        View.get?_outOfBounds bp i (bLen ▸ Nat.le_of_not_lt inside)]
  · simp [View.sub?, fits, ← same.length]

private theorem Same.varintAux {a b : View} (same : Same a b) (fuel offset acc : Nat) :
    Varint.readAux? a fuel offset acc = Varint.readAux? b fuel offset acc := by
  induction fuel generalizing offset acc with
  | zero => rfl
  | succ fuel ih =>
    cases fuel with
    | zero => simp [Varint.readAux?, same.get]
    | succ more => simp [Varint.readAux?, same.get, ih]

private theorem Same.varintNat {a b : View} (same : Same a b) (offset : Nat) :
    Varint.readNat? a offset = Varint.readNat? b offset := same.varintAux 9 offset 0

private theorem Same.varint {a b : View} (same : Same a b) (offset : Nat) :
    Varint.read? a offset = Varint.read? b offset := by
  simp [Varint.read?, same.varintNat]

private theorem Same.be {a b : View} (same : Same a b) (offset width : Nat) :
    a.be? offset width = b.be? offset width := by
  simp [View.be?, same.get]

private theorem Same.cell {a b : View} (same : Same a b) (start : Nat) :
    TableLeaf.cell? a start = TableLeaf.cell? b start := by
  unfold TableLeaf.cell?
  simp only [same.varintNat, same.varint, same.length]
  congr 1
  funext data
  rcases data with ⟨length, keyOffset⟩
  congr 1
  funext _
  congr 1
  funext data
  rcases data with ⟨key, payloadOffset⟩
  have payloads := same.slice payloadOffset length
  cases h₁ : a.sub? payloadOffset length <;> cases h₂ : b.sub? payloadOffset length <;>
    simp_all

private theorem Same.read {a b : View} (same : Same a b) (base : Nat) :
    TableLeaf.read? a base = TableLeaf.read? b base := by
  simp [TableLeaf.read?, same.length, same.get, same.be, same.cell]

theorem read_materialized (view : View) (base : Nat) :
    TableLeaf.read? (View.ofBytes view.materialize) base = TableLeaf.read? view base :=
  ((same_copy view).read base).symm

end Silmaril.Proofs.Formats.Sqlite.TableLeaf.Materialize
