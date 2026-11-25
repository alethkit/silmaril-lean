module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
import Silmaril.Machine.SqliteVfs.FileView.Thms
import Silmaril.Formats.Sqlite.File.Thms
import Init.Data.ByteArray.Lemmas

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.TableLeaf

open Silmaril.Formats.Sqlite.File (View Image)
open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs

private theorem materialize_length (view : View) : view.materialize.length = view.length := by
  have bounded : view.start + view.length ≤ view.source.data.size := view.bounded
  simp [View.materialize, Silmaril.Formats.Bytes.length, Nat.min_eq_left bounded]

private theorem materialize_read (view : View) (i : Nat) (inside : i < view.length) :
    view.materialize.toList[i]? = view.get? i := by
  have withinCopy : i < view.materialize.data.size := by
    change i < view.materialize.length
    rw [materialize_length]
    exact inside
  have withinSource : view.start + i < view.source.data.size :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left inside _) view.bounded
  have listed : view.materialize.toList[i]? = some view.materialize.data[i] := by
    rw [Silmaril.Formats.Bytes.toList, Array.getElem?_toList,
      Array.getElem?_eq_getElem (show i < view.materialize.data.data.size from withinCopy)]
    rfl
  rw [listed]
  unfold View.get?
  rw [ite_eq_left inside, getElem?_pos view.source.data _ withinSource]
  exact congrArg some (ByteArray.getElem_extract withinCopy)

private theorem materialized (view : View) (bytes : Bytes) (length : bytes.length = view.length)
    (equal : ∀ i, i < view.length → bytes[i]? = view.get? i) :
    Silmaril.Formats.Bytes.ofList bytes = view.materialize := by
  apply Silmaril.Formats.Bytes.ext
  rw [Silmaril.Formats.Bytes.toList_ofList]
  apply List.ext_getElem?
  intro i
  by_cases inside : i < view.length
  · rw [equal i inside, materialize_read view i inside]
  · rw [List.getElem?_eq_none (length ▸ Nat.le_of_not_lt inside)]
    exact (List.getElem?_eq_none (by
      simpa [materialize_length] using Nat.le_of_not_lt inside)).symm


/-- Page-local observations used by the packed leaf parser. -/
private structure Same (a b : View) : Prop where
  length : a.length = b.length
  get (i : Nat) : a.get? i = b.get? i

private theorem same_copy (view : View) : Same view (View.ofBytes view.materialize) := by
  have length : (View.ofBytes view.materialize).length = view.length := materialize_length view
  refine ⟨length.symm, fun i => ?_⟩
  by_cases inside : i < view.length
  · have hcopy : i < (View.ofBytes view.materialize).length := length ▸ inside
    rw [← materialize_read view i inside]
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
  · rw [materialize_read a i inside, materialize_read b i (same.length ▸ inside), same.get]
  · have outside := Nat.le_of_not_lt inside
    rw [List.getElem?_eq_none (by simpa [materialize_length] using outside),
      List.getElem?_eq_none (by simpa [materialize_length, ← same.length] using outside)]

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

theorem image_page_fill_decode (capacity : Nat) (file : FileState) (image : Image) (number : Nat)
    (view : View) (handle : Handle) (cache : PageRead.Cache) (target base : Nat)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize)
    (owned : cache target = some .vacant) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    ∃ bytes, PageRead.fill (readOnly capacity) file cache target page =
      ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
      TableLeaf.read? (View.ofBytes (Silmaril.Formats.Bytes.ofList bytes)) base =
        TableLeaf.read? view base := by
  obtain ⟨bytes, fill, length, read⟩ :=
    FileView.image_page_fill capacity file image number view handle cache target snapshot found
      live range owned
  refine ⟨bytes, fill, ?_⟩
  rw [materialized view bytes length read]
  exact read_materialized view base

end Silmaril.Proofs.Machine.SqliteVfs.FileView.TableLeaf
