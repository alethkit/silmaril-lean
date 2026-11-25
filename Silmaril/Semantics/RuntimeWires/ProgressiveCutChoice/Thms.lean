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

/-- Transport an ordered cut across an interval with the same active wires. -/
theorem OrderedCut.relocate_active {kind : VertexSeparation} {d : Diagram S V W kind}
    {h k : ℝ} {wires : List (Fin W)} (cut : d.OrderedCut h wires)
    (same : ∀ w y, y ∈ Set.uIcc h k → (d.crosses w h ↔ d.crosses w y)) :
    d.OrderedCut k wires :=
  Proofs.ProgressiveCutChoice.relocate_active cut same

/-- Moving a cut within a vertex-free gap preserves the exact ordered wire list. -/
theorem OrderedCut.relocate {i : Fin (V + 1)} {h k : ℝ} {wires : List (Fin W)}
    (cut : d.OrderedCut h wires) (hh : h ∈ d.gap i) (hk : k ∈ d.gap i) :
    d.OrderedCut k wires :=
  Proofs.ProgressiveCutChoice.relocate hh hk cut

namespace Sweep

theorem joinRows_eq {n : ℕ} {a b : Fin (n + 1) → List O} (words : a = b)
    (r : ∀ i : Fin n, Sliced.Row S (a i.castSucc) (a i.succ))
    (q : ∀ i : Fin n, Sliced.Row S (b i.castSucc) (b i.succ))
    (rows : ∀ i, HEq (r i) (q i)) :
    (congrArg₂ (Sliced.Sheet S) (congrFun words 0) (congrFun words (Fin.last n))).mp
      (joinRows a r) = joinRows b q :=
  Proofs.ProgressiveCutChoice.joinRows_eq words r q rows

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
