module

public import Silmaril.Semantics.RuntimeWires.PolygonalSwap.Defs

@[expose] public section

/-!
# Slanted incident wires in the progressive box swap

This extends the local comparison with Román and Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.
See Definition 3.2, Figure 7, Lemma 3.4 and Theorem 3.6 (pp. 9:6–9:8).

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Polygonal

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {floor : ℝ} {e f : S.Edge}

/-- The two fixed external frontiers of a box, inside its horizontal slot.
Their positions may differ from the corresponding positions on the box. -/
structure ExternalPorts (b : Box S floor e) where
  input : Frontier (S.source e)
  output : Frontier (S.target e)
  input_inside : ∀ x ∈ input.positions, x ∈ Set.Ioo b.left b.right
  output_inside : ∀ x ∈ output.positions, x ∈ Set.Ioo b.left b.right

namespace ExternalPorts

variable {b : Box S floor e} (p : ExternalPorts b)

def incoming (h : BoxAltitude) (i : Fin (S.source e).length) : Strand (BoxAltitude.inputs h) :=
  connector (BoxAltitude.inputs h) p.input b.input i

def outgoing (h : BoxAltitude) (i : Fin (S.target e).length) : Strand (BoxAltitude.outputs h) :=
  connector (BoxAltitude.outputs h) b.output p.output i

def cell (h : BoxAltitude) : BoxCell S e → Set Point
  | .body => b.trace (BoxAltitude.body h)
  | .input i => (p.incoming h i).trace
  | .output i => (p.outgoing h i).trace

def column (h : BoxAltitude) : Set Point := ⋃ c, p.cell h c

end ExternalPorts

namespace BoxPair

variable (d : BoxPair S floor e f)

def slantedSnapshot (p : ExternalPorts d.first) (q : ExternalPorts d.second) (t : SwapTime) :
    Set Point :=
  p.column (firstAltitude t) ∪ q.column (secondAltitude t)

end BoxPair
end Silmaril.RuntimeWires.Polygonal
