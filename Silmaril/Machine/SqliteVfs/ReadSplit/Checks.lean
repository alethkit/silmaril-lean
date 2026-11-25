module

import Silmaril.Machine.SqliteVfs.ReadSplit.Thms
import Silmaril.Machine.SqliteVfs.Thms

namespace Silmaril.Machine.SqliteVfs.ReadSplit

private def file : FileState := ⟨[11, 22, 33, 44, 0, 77], some .readOnly, 0⟩
private def handle : Handle := ⟨0⟩

private def counted : Handler (FileState × Nat) :=
  fun state req =>
    let result := readOnly 8 state.1 req
    (result.1, result.2, state.2 + 1)

private theorem counted_law : ReadLaw counted Prod.fst where
  read state := (readOnly_lawful 8).2.1.read state.1
  fileSize state := (readOnly_lawful 8).2.1.fileSize state.1

example :
    let first := counted (file, 0) (.read handle 2 2)
    let second := counted first.2 (.read handle 4 3)
    let whole := counted (file, 0) (.read handle 2 5)
    combine first.1 second.1 = some (.shortRead [33, 44, 0, 77, 0]) ∧
      second.2.1 = whole.2.1 ∧ second.2.2 = 2 ∧ whole.2.2 = 1 := by decide

example :
    let first := counted (file, 0) (.read handle 2 2)
    let second := counted first.2 (.read handle 4 3)
    let whole := counted (file, 0) (.read handle 2 5)
    combine first.1 second.1 = some whole.1 ∧ second.2.1 = whole.2.1 ∧
      Trace.Valid counted (file, 0)
        [⟨.read handle 2 2, first.1⟩, ⟨.read handle 4 3, second.1⟩] second.2 ∧
      Trace.Valid counted (file, 0) [⟨.read handle 2 5, whole.1⟩] whole.2 :=
  reads_split counted_law (file, 0) handle (offset := 2) (left := 2) (right := 3)
    (by decide) (by decide) (by decide) (by decide)

example :
    combine ((readOnly 8 file (.read handle 0 2)).1)
      ((readOnly 8 file (.read handle 2 4)).1) = some (.ok [11, 22, 33, 44, 0, 77]) := by decide

example :
    combine ((readOnly 8 file (.read handle 0 0)).1)
      ((readOnly 8 file (.read handle 0 2)).1) = none := by decide

end Silmaril.Machine.SqliteVfs.ReadSplit
