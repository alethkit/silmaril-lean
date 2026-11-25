module

public import Silmaril.Semantics.RuntimeWires.ZeroRuntime.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ZeroRuntimeEquivalence.Erasure

@[expose] public section

/-!
# Pure representatives of the zero-runtime quotient

The zero-runtime step in Lemma 3.13 (p. 9:11) of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Presentation

open CategoryTheory

universe u v

/-- Erasure on quotient arrows between value-only boundaries. -/
def eraseValueMorphism {G : EffectfulPolygraph.{u,v}} {A B : Pure G}
    (f : (pureValues G).obj A ⟶ (pureValues G).obj B) : A ⟶ B :=
  Quotient.map
    (fun t => Diagram.reindex (eraseBoundary_values A.word) (eraseBoundary_values B.word)
      (erasePure t (runtimeCount_values A.word)))
    (fun _ _ h => by
      exact Proofs.ZeroRuntimeEquivalence.reindex_congr _ _
        (Proofs.ZeroRuntimeEquivalence.erase_congr h (runtimeCount_values A.word)))
    f

end Silmaril.RuntimeWires.Presentation
