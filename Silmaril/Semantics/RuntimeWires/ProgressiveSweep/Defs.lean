module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Defs
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# Finite sweep of a progressive polygonal graph

This develops the reverse slicing construction for the point-vertex
fragment of Definition 3.2 in Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5 (p. 9:6).
The paper's geometric comparison in Lemma 3.4 and Theorem 3.6 also depends
on the identification under planar isotopy.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} (d : Diagram S V W)

/-- The permutation of point vertices in increasing height order. -/
noncomputable def vertexOrder : Equiv.Perm (Fin V) := Tuple.sort d.vertexHeight

/-- The outer caps and sorted vertex heights, in one increasing sequence. -/
noncomputable def landmark : Fin (V + 2) → ℝ :=
  Fin.cons 0 (Fin.snoc (d.vertexHeight ∘ d.vertexOrder) 1)

/-- The open gap after the landmark with the given index. -/
noncomputable def gap (i : Fin (V + 1)) : Set ℝ :=
  Set.Ioo (d.landmark i.castSucc) (d.landmark i.succ)

/-- Choose one height in each open gap between successive landmarks. -/
structure Cuts where
  height : Fin (V + 1) → ℝ
  in_gap : ∀ i, height i ∈ d.gap i

/-- One interior cut in each open gap between successive landmarks. -/
noncomputable def cutHeight (i : Fin (V + 1)) : ℝ :=
  (d.landmark i.castSucc + d.landmark i.succ) / 2

/-- Index of a vertex in the sequence of landmarks, with the lower cap at zero. -/
noncomputable def vertexIndex (v : Fin V) : Fin (V + 2) := ((d.vertexOrder.symm v).castSucc).succ

noncomputable def startIndex (w : Fin W) : Fin (V + 2) :=
  (d.start w).elim 0 d.vertexIndex

noncomputable def finishIndex (w : Fin W) : Fin (V + 2) :=
  (d.finish w).elim (Fin.last (V + 1)) d.vertexIndex

/-- Read the vertex at an interior landmark, or `none` at a cap. -/
noncomputable def vertexAt (j : Fin (V + 2)) : Option (Fin V) :=
  Fin.cases none (Fin.lastCases none (fun i => some (d.vertexOrder i))) j

/-- The ordered wire list at each cut and the local incidence certificate
for each successive vertex. -/
structure Sweep where
  cuts : d.Cuts
  wires : Fin (V + 1) → List (Fin W)
  ordered : ∀ i, d.OrderedCut (cuts.height i) (wires i)
  event : ∀ i : Fin V, d.EventSlice (d.vertexOrder i)
    (cuts.height i.castSucc) (cuts.height i.succ)
  before : ∀ i, (event i).beforeWires = wires i.castSucc
  after : ∀ i, (event i).afterWires = wires i.succ

/-- All cut indices at which the specified original wire ID occurs. -/
def Sweep.wireCuts {d : Diagram S V W} (s : d.Sweep) (w : Fin W) : Finset (Fin (V + 1)) :=
  Finset.univ.filter (fun i => w ∈ s.wires i)

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
