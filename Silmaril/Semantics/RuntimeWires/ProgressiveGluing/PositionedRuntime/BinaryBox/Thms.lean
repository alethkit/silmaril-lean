module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.BinaryBox.Defs
import all Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.BinaryBox

public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O}
variable (e : S.Edge) {a b c d : O} (input : S.source e = [a, b]) (output : S.target e = [c, d])

/-- Draw a binary generator as four affine arms meeting at one point. -/
def binaryBox : FixedDrawing S (binaryCap S a b).profile (binaryCap S c d).profile :=
  Proofs.PositionedRuntime.BinaryBox.box e input output

theorem binaryBox_vertices : (binaryBox e input output).vertices = 1 := by rfl

theorem binaryBox_generator (i : Fin (binaryBox e input output).vertices) :
    (binaryBox e input output).drawing.generator i = e := by rfl

theorem binaryBox_noThrough (i : Fin (binaryBox e input output).wires)
    (j : Fin (binaryBox e input output).vertices) :
    ¬ (binaryBox e input output).drawing.crosses i ((binaryBox e input output).drawing.vertexHeight j) :=
  Proofs.PositionedRuntime.BinaryBox.box_noThrough e input output i j

theorem binaryBox_cells : (binaryBox e input output).readSheet.cells = [[.inr e]] :=
  Proofs.PositionedRuntime.BinaryBox.box_cells e input output

end Silmaril.RuntimeWires.ProgressiveGraph
