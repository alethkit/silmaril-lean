module

public import Silmaril.Semantics.RuntimeWires.PureInclusion.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.PureInclusion.Interpretation

@[expose] public section

namespace Silmaril.RuntimeWires.Presentation

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory

universe u v

/-- Interpret pure diagrams in the runtime category on value-only boundaries. -/
def pureValues (G : EffectfulPolygraph.{u,v}) : Pure G ⥤ Runtime G where
  obj X := valueWord X.word
  map := Quotient.lift pureTerm (fun _ _ h => by exact Proofs.PureInclusion.respect h)
  map_id _ := rfl
  map_comp f g := Quotient.inductionOn₂ f g (fun _ _ => rfl)

theorem pureValues_map_term {G : EffectfulPolygraph.{u,v}} {X Y : Pure G}
    (f : Diagram G.pure X.word Y.word) :
    (pureValues G).map (Diagram.Presented.ofTerm f) = pureTerm f :=
  rfl

/-- The functor of Lemma 3.12. It attaches an untouched runtime to a pure
diagram and carries each value word verbatim. -/
def pureInclusion (G : EffectfulPolygraph.{u,v}) : Pure G ⥤ Computations G where
  obj := pureObject
  map f := runtime G ◁ (pureValues G).map f
  map_id X := (tensorLeft (runtime G)).map_id ((pureValues G).obj X)
  map_comp f g := ((pureValues G ⋙ tensorLeft (runtime G)).map_comp f g)

end Silmaril.RuntimeWires.Presentation
