module

public import Silmaril.Semantics.RuntimeWires.Polygonal.Realization

public section

namespace Silmaril.RuntimeWires.Proofs.Polygonal

open Silmaril.RuntimeWires.Polygonal Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {A B : List O}

theorem read_realized_row (floor : ℝ) (r : Row S A B) :
    (Layer.realize floor r).readRow = r := by
  induction r generalizing floor with
  | empty => rfl
  | wire a r ih => simp only [Layer.realize, Layer.readRow, ih]
  | box e r ih => simp only [Layer.realize, Layer.readRow, ih]

theorem read_realized_sheet (height : ℝ) (p : Sheet S A B) :
    (Drawing.realize height p).readSheet = p := by
  induction p generalizing height with
  | empty => rfl
  | cons r p ih => simp only [Drawing.realize, Drawing.readSheet, read_realized_row, ih]

end Silmaril.RuntimeWires.Proofs.Polygonal
