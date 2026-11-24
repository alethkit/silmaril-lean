module

public import Silmaril.Formats.Sqlite.File.Defs

/-! Big-endian fields and the database header for a two-page UTF-8 image. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.File.Write

def be (width value : Nat) : List UInt8 :=
  (List.range width).map fun index => UInt8.ofNat (value / 256 ^ (width - 1 - index))

@[simp] theorem be_length (width value : Nat) : (be width value).length = width := by
  simp [be]

def pageSize : Nat := 512

/-- Format 4, legacy read/write versions, no reserved bytes, and two pages.
Both page-count validity counters are one. The writer version is unspecified. -/
def header : List UInt8 :=
  headerMagic ++ be 2 pageSize ++ [1, 1, 0, 64, 32, 32] ++
    [1, 2, 0, 0, 1, 4, 0, 0, 1, 0, 0, 0].flatMap (be 4) ++
    List.replicate 20 0 ++ be 4 1 ++ be 4 0

theorem header_length : header.length = 100 := rfl

end Silmaril.Formats.Sqlite.File.Write
