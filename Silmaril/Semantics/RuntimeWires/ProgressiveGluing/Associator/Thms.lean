module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Associator.Defs
public import Mathlib.Topology.Homeomorph.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Vertices

public section

/-!
# Fixed-contact triple gluing

The associator compares two actual collared vertical gluings by reusing
the typed matches at the induced outer caps and rescaling the five slabs.
This is a geometric part of sequential juxtaposition in Figure 7 and
Lemma 3.4 of Mario Román and Paweł Sobociński, *String Diagrams for
Premonoidal Categories*, arXiv:2305.06075v5, p. 9:7. The pinned PDF
SHA-256 is `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.IncidenceEquiv

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W V' W' : ℕ}
variable {a : Diagram S V W .point} {b : Diagram S V' W' .point}

theorem start (p : a.IncidenceEquiv b) (w : Fin W) :
    b.start (p.wire w) = (a.start w).map p.vertex :=
  Proofs.CollarAssociator.incidence_start p w

theorem finish (p : a.IncidenceEquiv b) (w : Fin W) :
    b.finish (p.wire w) = (a.finish w).map p.vertex :=
  Proofs.CollarAssociator.incidence_finish p w

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.IncidenceEquiv

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.OrderedVerticalMatch

open PartialVerticalMatch
universe u v
variable {O : Type u} {S : Signature.{u,v} O} {L M R A B C : ℕ}
variable {d : ProgressiveGraph.Diagram S L A .point} {e : ProgressiveGraph.Diagram S M B .point}
variable {f : ProgressiveGraph.Diagram S R C .point}
variable (m : d.OrderedVerticalMatch e) (n : e.OrderedVerticalMatch f)

/-- Reuse the second match at the actual cap of the first glued pair. -/
noncomputable def attachAfter : m.glue.OrderedVerticalMatch f :=
  Proofs.CollarAssociator.after m n

/-- Reuse the first match at the actual cap of the second glued pair. -/
noncomputable def attachBefore : d.OrderedVerticalMatch n.glue :=
  Proofs.CollarAssociator.before m n

noncomputable def lowerWireId (a : Fin A) : Fin (wireCount m.lowerJoin.glue e) :=
  Proofs.CollarAssociator.leftWire m a

noncomputable def upperWireId (b : Fin B) : Fin (wireCount m.lowerJoin.glue e) :=
  Proofs.CollarAssociator.rightWire m b

/-- Typed incidence of the two parenthesizations, with identities on the
three original sets of generator occurrences and the induced wire renaming. -/
noncomputable def assocIncidence : (m.attachAfter n).glue.IncidenceEquiv (m.attachBefore n).glue :=
  Proofs.CollarAssociator.assocIncidence m n

theorem assoc_wire_first (a : Fin A) :
    (m.assocIncidence n).wire ((m.attachAfter n).lowerWireId (m.lowerWireId a)) =
      (m.attachBefore n).lowerWireId a :=
  Proofs.CollarAssociator.toRight_A m n a

theorem assoc_wire_middle (b : Fin B) :
    (m.assocIncidence n).wire ((m.attachAfter n).lowerWireId (m.upperWireId b)) =
      (m.attachBefore n).upperWireId (n.lowerWireId b) :=
  Proofs.CollarAssociator.toRight_B m n b

theorem assoc_wire_last (c : Fin C) :
    (m.assocIncidence n).wire ((m.attachAfter n).upperWireId c) =
      (m.attachBefore n).upperWireId (n.upperWireId c) :=
  Proofs.CollarAssociator.toRight_C m n c

/-- The plane homeomorphism mapping the left-associated slab heights to
the right-associated heights and leaving horizontal coordinates fixed. -/
noncomputable def assocHeight : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  Proofs.CollarAssociator.Height.pointMap

theorem assocHeight_fixed (p : ℝ × ℝ) (h : p.2 ≤ 0 ∨ 1 ≤ p.2) :
    assocHeight p = p :=
  Prod.ext rfl (Proofs.CollarAssociator.Height.outside_height h)

theorem assoc_vertex (j : Fin ((L + M) + R)) :
    assocHeight ((m.attachAfter n).glue.vertexX j, (m.attachAfter n).glue.vertexHeight j) =
      ((m.attachBefore n).glue.vertexX ((m.assocIncidence n).vertex j),
        (m.attachBefore n).glue.vertexHeight ((m.assocIncidence n).vertex j)) :=
  Proofs.CollarAssociator.assoc_vertex_point m n j

/-- The height homeomorphism sends each full left-associated wire trace to
the corresponding trace of the actual right-associated gluing. -/
theorem assoc_trace (w : Fin (wireCount (m.attachAfter n).lowerJoin.glue f)) :
    assocHeight '' ((m.attachAfter n).glue.wire w).trace =
      ((m.attachBefore n).glue.wire ((m.assocIncidence n).wire w)).trace :=
  Proofs.CollarAssociator.assoc_trace m n w

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.OrderedVerticalMatch
