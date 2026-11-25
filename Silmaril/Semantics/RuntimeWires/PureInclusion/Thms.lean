module

public import Silmaril.Semantics.RuntimeWires.PureInclusion.Values
import Silmaril.Proofs.Semantics.RuntimeWires.PureInclusion.Strict

public section

namespace Silmaril.RuntimeWires.Presentation

open CategoryTheory
open scoped MonoidalCategory

universe u v

variable {G : EffectfulPolygraph.{u,v}}

@[simp] theorem pureInclusion_obj (X : Pure G) : (pureInclusion G).obj X = pureObject X :=
  rfl

/-- On a pure term, the functor tensors its interpretation on the left by the runtime identity. -/
theorem pureInclusion_map_term {X Y : Pure G} (f : Diagram G.pure X.word Y.word) :
    (show (pureObject X).boundary ⟶ (pureObject Y).boundary from
      (pureInclusion G).map (Diagram.Presented.ofTerm f)) = runtime G ◁ pureTerm f :=
  rfl

/-- Choosing a pure morphism proves both exchange laws against arbitrary computations. -/
theorem pureInclusion_central {X Y : Pure G} (f : X ⟶ Y) :
    PremonoidalCategory.IsCentral ((pureInclusion G).map f) :=
  Proofs.PureInclusion.image_central f

theorem pureInclusion_whiskerLeft (X : Pure G) {Y Z : Pure G} (f : Y ⟶ Z) :
    (pureInclusion G).obj X ◁ (pureInclusion G).map f = (pureInclusion G).map (X ◁ f) :=
  Proofs.PureInclusion.map_left X f

theorem pureInclusion_whiskerRight {X Y : Pure G} (f : X ⟶ Y) (Z : Pure G) :
    (pureInclusion G).map f ▷ (pureInclusion G).obj Z = (pureInclusion G).map (f ▷ Z) :=
  Proofs.PureInclusion.map_right f Z

/-- The chosen pure inclusion uses identity tensor and unit comparisons. -/
instance pureInclusionStrong (G : EffectfulPolygraph.{u,v}) :
    Functor.StrongPremonoidal (pureInclusion G) where
  unitIso := Iso.refl _
  tensorIso _ _ := Iso.refl _
  tensor_naturality_left {_ _} f Z := by
    exact (Proofs.PureInclusion.strong G).tensor_naturality_left f Z
  tensor_naturality_right X {_ _} f := by
    exact (Proofs.PureInclusion.strong G).tensor_naturality_right X f
  associativity X Y Z := by exact (Proofs.PureInclusion.strong G).associativity X Y Z
  left_unitality X := by exact (Proofs.PureInclusion.strong G).left_unitality X
  right_unitality X := by exact (Proofs.PureInclusion.strong G).right_unitality X
  map_central f := pureInclusion_central f

theorem pureInclusion_unitIso :
    Functor.StrongPremonoidal.unitIso (J := pureInclusion G) = Iso.refl _ := rfl

theorem pureInclusion_tensorIso (X Y : Pure G) :
    Functor.StrongPremonoidal.tensorIso (J := pureInclusion G) X Y = Iso.refl _ := rfl

end Silmaril.RuntimeWires.Presentation
