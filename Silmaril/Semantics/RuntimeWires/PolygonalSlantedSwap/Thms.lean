module

public import Silmaril.Semantics.RuntimeWires.PolygonalSlantedSwap.Defs
public import Silmaril.Semantics.RuntimeWires.PolygonalSwap.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.PolygonalSlantedSwap.Transport
import Silmaril.Semantics.RuntimeWires.Polygonal.Thms

public section

namespace Silmaril.RuntimeWires.Polygonal

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {floor : ℝ} {e f : S.Edge}

namespace ExternalPorts

variable {b : Box S floor e} (p : ExternalPorts b)

theorem column_bounds (h : BoxAltitude) :
    p.column h ⊆ Set.Icc b.left b.right ×ˢ Set.Icc 0 6 :=
  Proofs.PolygonalSlantedSwap.column_bounds p h

theorem incoming_disjoint (h : BoxAltitude) {i j : Fin (S.source e).length} (hij : i ≠ j) :
    Disjoint (p.incoming h i).trace (p.incoming h j).trace :=
  connector_trace_disjoint _ _ _ hij

theorem outgoing_disjoint (h : BoxAltitude) {i j : Fin (S.target e).length} (hij : i ≠ j) :
    Disjoint (p.outgoing h i).trace (p.outgoing h j).trace :=
  connector_trace_disjoint _ _ _ hij

theorem input_output_disjoint (h : BoxAltitude) (i : Fin (S.source e).length)
    (j : Fin (S.target e).length) :
    Disjoint (p.incoming h i).trace (p.outgoing h j).trace :=
  Proofs.PolygonalSlantedSwap.input_output_disjoint p h i j

theorem incoming_contact (h : BoxAltitude) (i : Fin (S.source e).length) :
    (p.incoming h i).trace ∩ b.trace (BoxAltitude.body h) = {(b.input.coordinate i, h.val)} :=
  Proofs.PolygonalSlantedSwap.incoming_contact p h i

theorem outgoing_contact (h : BoxAltitude) (i : Fin (S.target e).length) :
    (p.outgoing h i).trace ∩ b.trace (BoxAltitude.body h) = {(b.output.coordinate i, h.val + 1)} :=
  Proofs.PolygonalSlantedSwap.outgoing_contact p h i

end ExternalPorts

namespace BoxPair

variable (d : BoxPair S floor e f)

theorem slanted_columns_disjoint (p : ExternalPorts d.first) (q : ExternalPorts d.second)
    (h k : BoxAltitude) : Disjoint (p.column h) (q.column k) :=
  Proofs.PolygonalSlantedSwap.slanted_columns_disjoint d p q h k

theorem slanted_snapshot_inside (p : ExternalPorts d.first) (q : ExternalPorts d.second)
    (t : SwapTime) : d.slantedSnapshot p q t ⊆ d.rectangle :=
  Proofs.PolygonalSlantedSwap.slanted_snapshot_inside d p q t

/-- The same ambient homeomorphism carries each cell to its exact affine trace. -/
theorem slanted_first_cell_image (p : ExternalPorts d.first) (t : SwapTime) (c : BoxCell S e) :
    d.deformation t '' (Subtype.val ⁻¹' p.cell (firstAltitude swapStart) c) =
      Subtype.val ⁻¹' p.cell (firstAltitude t) c :=
  Proofs.PolygonalSlantedSwap.slanted_first_cell d p t c

theorem slanted_second_cell_image (q : ExternalPorts d.second) (t : SwapTime) (c : BoxCell S f) :
    d.deformation t '' (Subtype.val ⁻¹' q.cell (secondAltitude swapStart) c) =
      Subtype.val ⁻¹' q.cell (secondAltitude t) c :=
  Proofs.PolygonalSlantedSwap.slanted_second_cell d q t c

theorem slanted_snapshot_image (p : ExternalPorts d.first) (q : ExternalPorts d.second)
    (t : SwapTime) :
    d.deformation t '' (Subtype.val ⁻¹' d.slantedSnapshot p q swapStart) =
      Subtype.val ⁻¹' d.slantedSnapshot p q t :=
  Proofs.PolygonalSlantedSwap.slanted_snapshot_image d p q t

end BoxPair
end Silmaril.RuntimeWires.Polygonal
