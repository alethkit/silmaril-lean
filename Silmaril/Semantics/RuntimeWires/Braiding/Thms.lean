module

public import Silmaril.Semantics.RuntimeWires.Braiding.Defs

public section

namespace Silmaril.RuntimeWires.Presentation

universe u v

/-- The hom-set bijection in Theorem 3.14, independently of the freeness assertion. -/
noncomputable def leftmostEquiv {G : EffectfulPolygraph.{u,v}} (A B : List G.Obj) :
    Clique.Hom (braidClique A) (braidClique B) ≃
      Hom G (none :: values A) (none :: values B) :=
  Clique.componentEquiv (braidClique A) (braidClique B) 0 0

theorem leftmostEquiv_apply {G : EffectfulPolygraph.{u,v}} {A B : List G.Obj}
    (f : Clique.Hom (braidClique A) (braidClique B)) :
    leftmostEquiv A B f = f.app 0 0 :=
  Clique.componentEquiv_apply 0 0 f

end Silmaril.RuntimeWires.Presentation
