module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.VertexFree
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Incidence
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Vertices
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Whiskering.Pieces

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.EmptyWhiskering

open ProgressiveGraph CollarAssociator
open CapClasses (glue matching match_slot incidence_trans)
open CapRecoordination (inputWires outputWires no_vertex)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c d : CapProfile O}

/-- Exact embeddings into the actual collared composite. -/
def lowerEmbedding (p : FixedDrawing S a b) (q : FixedDrawing S b c) :
    Fin p.wires → Fin (glue p q).wires :=
  leftWire (matching p q)

def upperEmbedding (p : FixedDrawing S a b) (q : FixedDrawing S b c) :
    Fin q.wires → Fin (glue p q).wires :=
  rightWire (matching p q)

section Prefix

variable (r : FixedDrawing S a b) (p : FixedDrawing S b c) (hr : r.vertices = 0)
local notation "m" => matching r p

theorem prefix_wire (i : Fin b.size) :
    lowerEmbedding r p (r.output i).val = upperEmbedding r p (p.input i).val :=
  (wire_contact m (r.output i)).trans (congrArg (fun w => rightWire m w.val) (match_slot r p i))

def prefixVertex : Fin p.vertices ≃ Fin (r.vertices + p.vertices) :=
  finCongr (by simp only [hr, Nat.zero_add])

theorem prefixVertex_apply (j : Fin p.vertices) : prefixVertex r p hr j = Fin.natAdd r.vertices j := by
  apply Fin.ext
  simp [prefixVertex, hr]

/-- The prefix has no generators and every prefix wire meets the splice,
so the ordered core incidence indexes the entire composite. -/
def prefixIncidence : p.drawing.IncidenceEquiv (glue r p).drawing where
  vertex := prefixVertex r p hr
  wire := Equiv.ofBijective (rightWire m) ⟨right_injective m, fun w => by
    rcases wire_cases m w with ⟨i, eq⟩ | existing
    · obtain ⟨j, rfl⟩ := (outputWires r hr).surjective i
      exact ⟨(p.input j).val, (prefix_wire r p j).symm.trans eq⟩
    · exact existing⟩
  generator j := (congrArg (m).glue.generator (prefixVertex_apply r p hr j)).trans (generator_upper m j)
  label := right_label m
  inputs j := (congrArg (m).glue.inputs (prefixVertex_apply r p hr j)).trans (inputs_upper m j)
  outputs j := (congrArg (m).glue.outputs (prefixVertex_apply r p hr j)).trans (outputs_upper m j)

end Prefix

section Suffix

variable (p : FixedDrawing S a b) (s : FixedDrawing S b c) (hs : s.vertices = 0)
local notation "m" => matching p s

theorem suffix_wire (i : Fin b.size) :
    upperEmbedding p s (s.input i).val = lowerEmbedding p s (p.output i).val :=
  (prefix_wire p s i).symm

def suffixVertex : Fin p.vertices ≃ Fin (p.vertices + s.vertices) :=
  finCongr (by simp only [hs, Nat.add_zero])

theorem suffixVertex_apply (j : Fin p.vertices) : suffixVertex p s hs j = Fin.castAdd s.vertices j := by
  apply Fin.ext
  rfl

/-- Every suffix wire meets the splice and is indexed by a core wire. -/
def suffixIncidence : p.drawing.IncidenceEquiv (glue p s).drawing where
  vertex := suffixVertex p s hs
  wire := Equiv.ofBijective (leftWire m) ⟨left_injective m, fun w => by
    rcases wire_cases m w with existing | ⟨i, eq⟩
    · exact existing
    · obtain ⟨j, rfl⟩ := (inputWires s hs).surjective i
      exact ⟨(p.output j).val, (suffix_wire p s j).symm.trans eq⟩⟩
  generator j := (congrArg (m).glue.generator (suffixVertex_apply p s hs j)).trans (generator_lower m j)
  label := left_label m
  inputs j := (congrArg (m).glue.inputs (suffixVertex_apply p s hs j)).trans (inputs_lower m j)
  outputs j := (congrArg (m).glue.outputs (suffixVertex_apply p s hs j)).trans (outputs_lower m j)

end Suffix

section Frame

variable (r : FixedDrawing S a b) (p : FixedDrawing S b c) (s : FixedDrawing S c d)
variable (hr : r.vertices = 0) (hs : s.vertices = 0)

abbrev framed := glue (glue r p) s

def frameIncidence : p.drawing.IncidenceEquiv (framed r p s).drawing :=
  incidence_trans (prefixIncidence r p hr) (suffixIncidence (glue r p) s hs)

abbrev embedWire := (frameIncidence r p s hr hs).wire

theorem frame_vertex_index (j : Fin p.vertices) :
    (frameIncidence r p s hr hs).vertex j = Fin.castAdd s.vertices (Fin.natAdd r.vertices j) := by
  change suffixVertex (glue r p) s hs (prefixVertex r p hr j) = _
  rw [prefixVertex_apply, suffixVertex_apply]

theorem frame_vertexX (j : Fin p.vertices) :
    (framed r p s).drawing.vertexX ((frameIncidence r p s hr hs).vertex j) = p.drawing.vertexX j := by
  rw [frame_vertex_index]
  exact (vertexX_lower (matching (glue r p) s) (Fin.natAdd r.vertices j)).trans
    (vertexX_upper (matching r p) j)

theorem frame_vertexHeight (j : Fin p.vertices) :
    (framed r p s).drawing.vertexHeight ((frameIncidence r p s hr hs).vertex j) =
      Height.leftPlacement 2 (p.drawing.vertexHeight j) := by
  rw [frame_vertex_index]
  exact (height_lower (matching (glue r p) s) (Fin.natAdd r.vertices j)).trans
    (congrArg Height.lower (height_upper (matching r p) j))

theorem prefix_name (i : Fin b.size) :
    lowerEmbedding (glue r p) s (lowerEmbedding r p (r.output i).val) =
      embedWire r p s hr hs (p.input i).val :=
  congrArg (lowerEmbedding (glue r p) s) (prefix_wire r p i)

theorem core_output (i : Fin c.size) :
    ((glue r p).output i).val = upperEmbedding r p (p.output i).val :=
  outputCap_val (matching r p) (p.output i)

theorem suffix_name (i : Fin c.size) :
    upperEmbedding (glue r p) s (s.input i).val = embedWire r p s hr hs (p.output i).val := by
  change upperEmbedding (glue r p) s (s.input i).val =
    lowerEmbedding (glue r p) s (upperEmbedding r p (p.output i).val)
  exact (suffix_wire (a := a) (b := c) (c := d) (glue r p) s i).trans
    (congrArg (lowerEmbedding (glue r p) s) (core_output r p i))

end Frame

end Silmaril.RuntimeWires.Proofs.EmptyWhiskering
