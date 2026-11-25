module

public import Silmaril.Semantics.RuntimeWires.PolygonalCuts.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.PolygonalCuts.Reconstruction

@[expose] public section

namespace Silmaril.RuntimeWires.Polygonal.Slab.Cut

variable {slab : Slab} (c : slab.Cut)

/-- The lower piece is the original trace clipped at the cut height. -/
theorem lower_trace (s : Strand slab) :
    (c.lowerStrand s).trace = s.trace ∩ {z | z.2 ≤ c.height} :=
  Proofs.PolygonalCuts.lower_trace c s

/-- The upper piece is the original trace clipped at the cut height. -/
theorem upper_trace (s : Strand slab) :
    (c.upperStrand s).trace = s.trace ∩ {z | c.height ≤ z.2} :=
  Proofs.PolygonalCuts.upper_trace c s

/-- Joining the two pieces recovers the original closed segment as a planar set. -/
theorem join_trace (s : Strand slab) :
    (c.lowerStrand s).trace ∪ (c.upperStrand s).trace = s.trace :=
  Proofs.PolygonalCuts.join_trace c s

/-- The pieces share just the point at the cut. -/
theorem contact_at_cut (s : Strand slab) :
    (c.lowerStrand s).trace ∩ (c.upperStrand s).trace = {(c.coordinate s, c.height)} :=
  Proofs.PolygonalCuts.contact_at_cut c s

variable {O : Type*} {A : List O}

/-- Each ordered port at the cut is computed from the corresponding original strand. -/
theorem frontier_coordinate (p q : Frontier A) (i : Fin A.length) :
    (c.frontier p q).coordinate i = c.coordinate (connector slab p q i) :=
  Proofs.PolygonalCuts.frontier_coordinate c p q i

/-- Joining the original input ports to the cut ports draws the lower pieces. -/
theorem lower_connector (p q : Frontier A) (i : Fin A.length) :
    connector c.lower p (c.frontier p q) i = c.lowerStrand (connector slab p q i) :=
  Proofs.PolygonalCuts.lower_connector c p q i

/-- Joining the cut ports to the original output ports draws the upper pieces. -/
theorem upper_connector (p q : Frontier A) (i : Fin A.length) :
    connector c.upper (c.frontier p q) q i = c.upperStrand (connector slab p q i) :=
  Proofs.PolygonalCuts.upper_connector c p q i

/-- Refining the connector by a cut leaves its covered planar set unchanged. -/
theorem connector_join (p q : Frontier A) (z : Point) :
    ((Part.connector c.lower p (c.frontier p q)).Contains z ∨
      (Part.connector c.upper (c.frontier p q) q).Contains z) ↔
    (Part.connector slab p q).Contains z :=
  Proofs.PolygonalCuts.connector_join c p q z

/-- The two connector pieces share exactly the points of the typed frontier. -/
theorem connector_contact (p q : Frontier A) (z : Point) :
    ((Part.connector c.lower p (c.frontier p q)).Contains z ∧
      (Part.connector c.upper (c.frontier p q) q).Contains z) ↔
    ∃ i : Fin A.length, z = ((c.frontier p q).coordinate i, c.height) :=
  Proofs.PolygonalCuts.connector_contact c p q z

end Silmaril.RuntimeWires.Polygonal.Slab.Cut
