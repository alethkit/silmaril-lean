module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarCombined.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Congruence
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Assoc

public section

/-!
# Cap-relative geometric equivalence and vertical gluing

The relation uses ambient endpoint homeomorphisms and explicit typed
trace and vertex correspondence. It includes supported fixed-cap
motions and the fixed-contact height associator. The fixed interfaces
record the horizontal coordinates as well as the ordered labels.
The geometric construction concerns Lemma 3.4 and Figure 7 of Mario
Román and Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5, p. 9:7. The pinned PDF SHA-256 is
`8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

namespace CapHomeomorph

/-- Conjugation by the affine placement of a half slab. -/
noncomputable def place (offset : ℝ) (f : CapHomeomorph) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  Proofs.CapClasses.placed offset f

noncomputable def placeHeight (offset : ℝ) (f : CapHomeomorph) : ℝ ≃ₜ ℝ :=
  Proofs.CapClasses.placedHeight offset f

theorem place_height (offset : ℝ) (f : CapHomeomorph) (z : ℝ × ℝ) :
    (place offset f z).2 = placeHeight offset f z.2 :=
  Proofs.CapClasses.placed_height_eq offset f z

theorem place_increasing (offset : ℝ) (f : CapHomeomorph) : StrictMono (placeHeight offset f) :=
  Proofs.CapClasses.placed_strict offset f

theorem place_fixed (offset : ℝ) (f : CapHomeomorph) (z : ℝ × ℝ)
    (h : z.2 ≤ halfHeight offset 0 ∨ halfHeight offset 1 ≤ z.2) :
    place offset f z = z :=
  Proofs.CapClasses.placed_fixed offset f z h

/-- The two conjugated maps compose across their fixed shared cap. -/
noncomputable def paste (f g : CapHomeomorph) : CapHomeomorph :=
  Proofs.CapClasses.paste f g

theorem paste_lower (f g : CapHomeomorph) (z : ℝ × ℝ) (h : z.2 ≤ 1 / 2) :
    (f.paste g).plane z = place 0 f z :=
  Proofs.CapClasses.paste_lower f g z h

theorem paste_upper (f g : CapHomeomorph) (z : ℝ × ℝ) (h : 1 / 2 ≤ z.2) :
    (f.paste g).plane z = place 1 g z :=
  Proofs.CapClasses.paste_upper f g z h

end CapHomeomorph

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

namespace Diagram.CapComparison

variable {V W : ℕ} {d : Diagram S V W .point}

def ofMotion (p : d.AmbientMotion) (t : SlabIsotopy.Time) : d.CapComparison (p.drawing t) :=
  Proofs.CapClasses.motion_comparison p t

variable {L M R A B C : ℕ}
variable {l : Diagram S L A .point} {r : Diagram S R B .point} {s : Diagram S M C .point}

/-- Both operand motions and the collar motion are admitted by the relation. -/
noncomputable def ofCombinedMotion (m : l.OrderedVerticalMatch r) (p q : PolygonalCollar m.collarSpec)
    (u : l.AmbientMotion) (v : r.AmbientMotion) (t : SlabIsotopy.Time) :
    (m.glueWith p).CapComparison ((m.glueWithMotions p q u v).drawing t) :=
  ofMotion (m.glueWithMotions p q u v) t

/-- The associator changes height in the interior and fixes the outer cuts. -/
noncomputable def ofAssociator (m : l.OrderedVerticalMatch s) (n : s.OrderedVerticalMatch r) :
    (m.attachAfter n).glue.CapComparison (m.attachBefore n).glue :=
  Proofs.CapClasses.assoc_comparison m n

end Diagram.CapComparison

namespace FixedDrawing

variable {a b c d : CapProfile O}

theorem Equivalent.refl (p : FixedDrawing S a b) : p.Equivalent p :=
  ⟨Proofs.CapClasses.compare_id p.drawing⟩

theorem Equivalent.symm {p q : FixedDrawing S a b} (h : p.Equivalent q) : q.Equivalent p :=
  h.map Proofs.CapClasses.compare_symm

theorem Equivalent.trans {p q r : FixedDrawing S a b}
    (h : p.Equivalent q) (k : q.Equivalent r) : p.Equivalent r :=
  h.elim fun h => k.map (Proofs.CapClasses.compare_trans h)

/-- The equivalence of the indexed caps used by the actual glue. -/
def matching (p : FixedDrawing S a b) (q : FixedDrawing S b c) :
    p.drawing.OrderedVerticalMatch q.drawing :=
  Proofs.CapClasses.matching p q

theorem matching_slot (p : FixedDrawing S a b) (q : FixedDrawing S b c) (i : Fin b.size) :
    (p.matching q).contact (p.output i) = q.input i :=
  Proofs.CapClasses.match_slot p q i

/-- Actual collared gluing with its remaining two ordered cap profiles. -/
noncomputable def thenDo (p : FixedDrawing S a b) (q : FixedDrawing S b c) :
    FixedDrawing S a c :=
  Proofs.CapClasses.glue p q

theorem thenDo_drawing (p : FixedDrawing S a b) (q : FixedDrawing S b c) :
    HEq (p.thenDo q).drawing (p.matching q).glue := by rfl

/-- Matching two straight through-wires yields one straight through-wire
at the same coordinate across the operands and the splice collar. -/
theorem thenDo_straight_through (p : FixedDrawing S a b) (q : FixedDrawing S b c)
    (i : Fin a.size) (j : Fin b.size) (k : Fin c.size) (x : ℝ)
    (hp : (p.input i).val = (p.output j).val) (hq : (q.input j).val = (q.output k).val)
    (px : ∀ y, p.drawing.x (p.input i).val y = x)
    (qx : ∀ y, q.drawing.x (q.input j).val y = x) :
    ((p.thenDo q).input i).val = ((p.thenDo q).output k).val ∧
      ∀ y, (p.thenDo q).drawing.x ((p.thenDo q).input i).val y = x :=
  Proofs.CapClasses.glue_straight_through p q i j k x hp hq px qx

/-- The placed operand comparisons preserve the full glued traces and
ordered incidence. The map is the identity on the common collar slab. -/
noncomputable def thenDo_comparison {p p' : FixedDrawing S a b} {q q' : FixedDrawing S b c}
    (h : p.drawing.CapComparison p'.drawing) (k : q.drawing.CapComparison q'.drawing) :
    (p.thenDo q).drawing.CapComparison (p'.thenDo q').drawing :=
  Proofs.CapClasses.glue_comparison h k

theorem thenDo_congr {p p' : FixedDrawing S a b} {q q' : FixedDrawing S b c}
    (h : p.Equivalent p') (k : q.Equivalent q') :
    (p.thenDo q).Equivalent (p'.thenDo q') :=
  h.elim fun h => k.map (thenDo_comparison h)

theorem thenDo_assoc (p : FixedDrawing S a b) (q : FixedDrawing S b c) (r : FixedDrawing S c d) :
    ((p.thenDo q).thenDo r).Equivalent (p.thenDo (q.thenDo r)) :=
  Proofs.CapClasses.glue_assoc p q r

end FixedDrawing
end Silmaril.RuntimeWires.ProgressiveGraph
