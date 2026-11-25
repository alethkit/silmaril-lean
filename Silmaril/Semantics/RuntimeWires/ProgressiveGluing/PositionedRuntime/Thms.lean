module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Padding
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Right
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Left

public noncomputable section

/-!
# Fixed-contact readout at a drawn runtime position

The sweep reads the ordered boundary at the drawn position. Clique braids
transport that component to the leftmost one. For Figure 10 of Román and
Sobociński, arXiv:2305.06075v5, the comparison covers any passive value word
on the right and a single passive value on the left of a drawing with no
active value contacts. The left comparison reads two geometric crossings.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.PositionedRuntimeCap

open CategoryTheory Presentation

universe u v
variable {G : EffectfulPolygraph.{u,v}} {X Y : PositionedRuntimeCap G}

theorem readClique_component (f : X.cap ⟶ Y.cap) :
    (readClique f).app X.position Y.position = component f :=
  (Clique.componentEquiv_apply X.position Y.position (readClique f)).symm.trans
    ((Clique.componentEquiv (braidClique X.word) (braidClique Y.word)
      X.position Y.position).apply_symm_apply (component f))

/-- The leftmost component is obtained by the two runtime braidings of the
original clique, starting from the independent geometric component. -/
theorem readClique_leftmost (f : X.cap ⟶ Y.cap) :
    (readClique f).app 0 0 =
      ((braidClique X.word).braid 0 X.position).hom ≫ component f ≫
        ((braidClique Y.word).braid 0 Y.position).inv := by
  have h := (readClique f).naturality 0 X.position 0 Y.position
  rw [readClique_component] at h
  calc
    _ = (readClique f).app 0 0 ≫ ((braidClique Y.word).braid 0 Y.position).hom ≫
        ((braidClique Y.word).braid 0 Y.position).inv := by simp
    _ = _ := by rw [← Category.assoc, h, Category.assoc]

end Silmaril.RuntimeWires.ProgressiveGraph.PositionedRuntimeCap

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory Presentation
open scoped MonoidalCategory

universe u v
variable {G : EffectfulPolygraph.{u,v}}

namespace FixedCap

theorem runtimeSweep_padRight {A B : FixedCap (signature G)} (f : A ⟶ B)
    (P : FixedCap (signature G)) :
    (runtimeSweep G).map (f ▷ P) =
      eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G))
        (beside_labels A P)) ≫
        (runtimeSweep G).map f ▷ (runtimeSweep G).obj P ≫
        eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G))
          (beside_labels B P).symm) := by
  exact Proofs.PositionedRuntime.map_right f P

theorem runtimeSweep_padLeft {A B : FixedCap (signature G)} (P : FixedCap (signature G))
    (f : A ⟶ B) :
    (runtimeSweep G).map (P ◁ f) =
      eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G))
        (beside_labels P A)) ≫
        (runtimeSweep G).obj P ◁ (runtimeSweep G).map f ≫
        eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G))
          (beside_labels P B).symm) := by
  exact Proofs.PositionedRuntime.map_left P f

end FixedCap

namespace FixedRuntimeCap

/-- The right-hand operation of Figure 10 for an arbitrary value-only idle word. -/
theorem toComputations_padRight {X Y : FixedRuntimeCap G} (P : FixedCap (signature G)) {W : List G.Obj}
    (types : P.types = values W) (f : X ⟶ Y) :
    (toComputations G).map (X := X.padRight P types) (Y := Y.padRight P types)
      (show X.padRight P types ⟶ Y.padRight P types from (show X.cap ⟶ Y.cap from f) ▷ P) =
    (Computations.whiskerRight (Computations.mk W)).map ((toComputations G).map f) := by
  exact Proofs.PositionedRuntime.pad_right P types f

/-- The left-hand operation of Figure 10 for one idle value and no active
value ports. Collared composition uses the drawn forward crossing,
the actual padded drawing, and the drawn reverse crossing. -/
theorem toComputations_leftScalar (x : G.Obj) {A B E H : FixedCap (signature G)}
    (P : FixedCap (signature G)) (hp : P.types = [some x]) (ha : A.types = [none])
    (hb : B.types = [none]) (he : E.types = [none, some x]) (hh : H.types = [none, some x])
    (f : A ⟶ B) (enter : IsolatedRuntimeGenerator (.moveRight x) E (P.beside A))
    (leave : IsolatedRuntimeGenerator (.moveLeft x) (P.beside B) H) :
    (toComputations G).map (X := ⟨E, [x], he⟩) (Y := ⟨H, [x], hh⟩)
      (show (⟨E, [x], he⟩ : FixedRuntimeCap G) ⟶ ⟨H, [x], hh⟩ from
        show E ⟶ H from
          FixedCap.ofDrawing (a := E) (b := P.beside A) enter.drawing ≫ P ◁ f ≫
            FixedCap.ofDrawing (a := P.beside B) (b := H) leave.drawing) =
    (Computations.whiskerLeft (Computations.mk [x])).map
      ((toComputations G).map (X := ⟨A, [], ha⟩) (Y := ⟨B, [], hb⟩) f) := by
  exact Proofs.PositionedRuntime.left_scalar x P hp ha hb he hh f enter leave

end FixedRuntimeCap
end Silmaril.RuntimeWires.ProgressiveGraph
