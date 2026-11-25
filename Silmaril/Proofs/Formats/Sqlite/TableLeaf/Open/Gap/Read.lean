module

public import Silmaril.Formats.Sqlite.File.Header.Frame.Thms
public import Silmaril.Formats.Sqlite.TableLeaf.Frame.Thms
public import Silmaril.Formats.Sqlite.TableLeaf.Open.Thms
import Silmaril.Formats.Sqlite.File.Thms

public section

open Silmaril.Formats Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.TableLeaf.Open.Gap

private theorem byte_in_source (view : File.View) (i : Nat) (inside : i < view.length) :
    view.get? i = (File.View.ofBytes view.source).get? (view.start + i) := by
  have inSource : view.start + i < view.source.length := by
    have := view.bounded
    omega
  simp [File.View.get?, File.View.ofBytes, inside, inSource]

private theorem beTwo_in_source (view : File.View) (i : Nat) (inside : i + 2 ≤ view.length) :
    view.be? i 2 = (File.View.ofBytes view.source).be? (view.start + i) 2 := by
  have range : List.range 2 = [0, 1] := rfl
  have first := byte_in_source view i (by omega)
  have second := byte_in_source view (i + 1) (by omega)
  simp [File.View.be?, range, first, second, Nat.add_assoc]

private theorem source_of_parse {source : Bytes} {image : File.Image}
    (parsed : File.parse? source = some image) : image.source = source := by
  unfold File.parse? at parsed
  obtain ⟨header, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  dsimp at parsed
  split at parsed
  · cases parsed
  · split at parsed <;> split at parsed <;> cases parsed <;> rfl

private def pageView (source : Bytes) (start : Nat) (fits : start + 512 ≤ source.length) :
    File.View := ⟨source, start, 512, fits⟩

private theorem page_of_parse (source : Bytes) (image : File.Image) (page : Nat)
    (parsed : File.parse? source = some image) (count : image.pageCount = 2)
    (pageSize : image.header.pageSize = 512) (pageMin : 0 < page) (pageMax : page ≤ 2)
    (fits : (page - 1) * 512 + 512 ≤ source.length) :
    image.page? page = some (pageView source ((page - 1) * 512) fits) := by
  simp [File.Image.page?, count, pageSize, Nat.ne_of_gt pageMin, pageMax, File.View.sub?,
    File.View.ofBytes, source_of_parse parsed, fits, pageView]

theorem open?_gap_eq (left right : Bytes) (leftSize : left.length = 1024)
    (rightSize : right.length = 1024)
    (catalogueCount catalogueContent tableCount tableContent : Nat)
    (catCount : (File.View.ofBytes left).be? 103 2 = some catalogueCount)
    (catContent : (File.View.ofBytes left).be? 105 2 = some catalogueContent)
    (tabCount : (File.View.ofBytes left).be? 515 2 = some tableCount)
    (tabContent : (File.View.ofBytes left).be? 517 2 = some tableContent)
    (same : ∀ i, i < 1024 →
      ¬ (108 + 2 * catalogueCount ≤ i ∧ i < catalogueContent ∧ i < 512) →
      ¬ (520 + 2 * tableCount ≤ i ∧ i < 512 + tableContent) →
        (File.View.ofBytes left).get? i = (File.View.ofBytes right).get? i) :
    TableLeaf.open? left = TableLeaf.open? right := by
  have length : left.length = right.length := leftSize.trans rightSize.symm
  have header : ∀ i, i < 100 → (File.View.ofBytes left).get? i = (File.View.ofBytes right).get? i :=
    fun i bound => same i (by omega) (by omega) (by omega)
  have descriptor := File.parse?_descriptor_frame left right length header
  cases lp : File.parse? left with
  | none =>
    cases rp : File.parse? right with
    | none => simp [TableLeaf.open?, lp, rp]
    | some ri => simp [lp, rp] at descriptor
  | some li =>
    cases rp : File.parse? right with
    | none => simp [lp, rp] at descriptor
    | some ri =>
      simp only [lp, rp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at descriptor
      obtain ⟨headers, counts, _⟩ := descriptor
      by_cases pageSize : li.header.pageSize = 512
      · by_cases count : li.pageCount = 2
        · let lc := pageView left 0 (by omega)
          let rc := pageView right 0 (by omega)
          let lt := pageView left 512 (by omega)
          let rt := pageView right 512 (by omega)
          have lcat : li.page? 1 = some lc := page_of_parse left li 1 lp count pageSize (by decide) (by decide) (by omega)
          have rcat : ri.page? 1 = some rc :=
            page_of_parse right ri 1 rp (counts ▸ count) (headers ▸ pageSize) (by decide) (by decide) (by omega)
          have ltab : li.page? 2 = some lt := page_of_parse left li 2 lp count pageSize (by decide) (by decide) (by omega)
          have rtab : ri.page? 2 = some rt :=
            page_of_parse right ri 2 rp (counts ▸ count) (headers ▸ pageSize) (by decide) (by decide) (by omega)
          have agree (start : Nat) (fits : start + 512 ≤ 1024) (i : Nat)
              (outsideCat : i < 512 → ¬ (108 + 2 * catalogueCount ≤ start + i ∧ start + i < catalogueContent ∧ start + i < 512))
              (outsideTab : i < 512 → ¬ (520 + 2 * tableCount ≤ start + i ∧ start + i < 512 + tableContent)) :
              (pageView left start (by omega)).get? i = (pageView right start (by omega)).get? i := by
            by_cases inside : i < 512
            · rw [byte_in_source _ i inside, byte_in_source _ i inside]
              exact same (start + i) (by omega) (outsideCat inside) (outsideTab inside)
            · rw [File.View.get?_outOfBounds _ i (by change 512 ≤ i; omega),
                File.View.get?_outOfBounds _ i (by change 512 ≤ i; omega)]
          have catalogue : TableLeaf.read? lc 100 = TableLeaf.read? rc 100 := by
            symm
            apply TableLeaf.read?_gap_eq lc rc 100 catalogueCount catalogueContent rfl
            · rw [beTwo_in_source lc _ (by change 105 ≤ 512; decide)]
              exact catCount
            · rw [beTwo_in_source lc _ (by change 107 ≤ 512; decide)]
              exact catContent
            · intro i lower upper
              apply agree 0 (by decide) i <;> intro inside <;> omega
            · intro i lower upper
              change i < 512 at upper
              apply agree 0 (by decide) i <;> intro inside <;> omega
          have table : TableLeaf.read? lt 0 = TableLeaf.read? rt 0 := by
            symm
            apply TableLeaf.read?_gap_eq lt rt 0 tableCount tableContent rfl
            · rw [beTwo_in_source lt _ (by change 5 ≤ 512; decide)]
              exact tabCount
            · rw [beTwo_in_source lt _ (by change 7 ≤ 512; decide)]
              exact tabContent
            · intro i lower upper
              apply agree 512 (by decide) i <;> intro inside <;> omega
            · intro i lower upper
              change i < 512 at upper
              apply agree 512 (by decide) i <;> intro inside <;> omega
          exact TableLeaf.open?_frame left right length header
            (by simpa only [lp, rp, lcat, rcat, Option.bind_some] using catalogue)
            (by simpa only [lp, rp, ltab, rtab, Option.bind_some] using table)
        · have rightCount : ri.pageCount ≠ 2 := by rw [← counts]; exact count
          simp [TableLeaf.open?, lp, rp, count, rightCount, guard, failure]
      · have otherPageSize : ri.header.pageSize ≠ 512 := by rw [← headers]; exact pageSize
        simp [TableLeaf.open?, lp, rp, pageSize, otherPageSize, guard, failure]

end Silmaril.Proofs.Formats.Sqlite.TableLeaf.Open.Gap
