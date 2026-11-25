module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Defs
public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapReadout.Boundaries

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedDrawing

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : CapProfile O}

/-- Read an independent geometric sweep at the ordered typed words of
the specified caps. -/
def readSheetAt (p : FixedDrawing S a b) (s : p.drawing.LayerSweep) :
    Sliced.Sheet S (List.ofFn a.label) (List.ofFn b.label) :=
  s.sheet.reindex (by exact Proofs.CapReadout.input_word p s) (by exact Proofs.CapReadout.output_word p s)

/-- Read the sheet using the midpoints of the actual gaps. -/
def readSheet (p : FixedDrawing S a b) : Sliced.Sheet S (List.ofFn a.label) (List.ofFn b.label) :=
  p.readSheetAt p.drawing.layerSweep

/-- Read an independently chosen serial schedule at the same cap words. -/
def readSerialAt (p : FixedDrawing S a b) (s : p.drawing.LayerSweep) (order : s.Schedule) :
    Sliced.Sheet S (List.ofFn a.label) (List.ofFn b.label) :=
  (s.serialSheet order).reindex
    (by exact Proofs.CapReadout.input_word p s) (by exact Proofs.CapReadout.output_word p s)

end Silmaril.RuntimeWires.ProgressiveGraph.FixedDrawing
