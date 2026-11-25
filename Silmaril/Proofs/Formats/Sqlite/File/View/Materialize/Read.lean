module

public import Silmaril.Formats.Sqlite.File.Defs
import Init.Data.ByteArray.Lemmas

public section

namespace Silmaril.Proofs.Formats.Sqlite.File.View

open Silmaril.Formats.Sqlite.File (View)

theorem materialize_length (view : View) : view.materialize.length = view.length := by
  have bounded : view.start + view.length ≤ view.source.data.size := view.bounded
  simp [View.materialize, Silmaril.Formats.Bytes.length, Nat.min_eq_left bounded]

theorem materialize_get? (view : View) (i : Nat) (inside : i < view.length) :
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

theorem ofList_eq_materialize (view : View) (bytes : List UInt8) (length : bytes.length = view.length)
    (equal : ∀ i, i < view.length → bytes[i]? = view.get? i) :
    Silmaril.Formats.Bytes.ofList bytes = view.materialize := by
  apply Silmaril.Formats.Bytes.ext
  rw [Silmaril.Formats.Bytes.toList_ofList]
  apply List.ext_getElem?
  intro i
  by_cases inside : i < view.length
  · rw [equal i inside, materialize_get? view i inside]
  · rw [List.getElem?_eq_none (length ▸ Nat.le_of_not_lt inside)]
    exact (List.getElem?_eq_none (by
      simpa [materialize_length] using Nat.le_of_not_lt inside)).symm

end Silmaril.Proofs.Formats.Sqlite.File.View
