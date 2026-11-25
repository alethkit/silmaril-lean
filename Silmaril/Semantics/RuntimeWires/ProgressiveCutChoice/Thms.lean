module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSweep.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveCutChoice.Independence

public section

/-!
# Independence of cut placement

For the finite distinct-height model of Definition 3.2 in Mario Román and
Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5 (p. 9:6), cuts can move within their open height gaps.
The typed sheets agree after transporting their actual boundary words.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W}

/-- Moving a cut within a vertex-free gap preserves the exact ordered wire list. -/
theorem OrderedCut.relocate {i : Fin (V + 1)} {h k : ℝ} {wires : List (Fin W)}
    (cut : d.OrderedCut h wires) (hh : h ∈ d.gap i) (hk : k ∈ d.gap i) :
    d.OrderedCut k wires :=
  Proofs.ProgressiveCutChoice.relocate hh hk cut

namespace Sweep

/-- Two choices of cuts read the same wire IDs in the same order at each gap. -/
theorem wires_eq (s t : d.Sweep) (i : Fin (V + 1)) : s.wires i = t.wires i :=
  Proofs.ProgressiveCutChoice.wires_eq s t i

/-- The extracted sheets agree after transporting the two boundary words
along the equalities of the corresponding ordered wire lists. -/
theorem sheet_eq (s t : d.Sweep) :
    (congrArg₂ (Sliced.Sheet S)
      (congrArg (List.map d.label) (s.wires_eq t 0))
      (congrArg (List.map d.label) (s.wires_eq t (Fin.last V)))).mp s.sheet = t.sheet :=
  Proofs.ProgressiveCutChoice.sheet_eq s t

end Sweep
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
