module

public import Silmaril.Semantics.RuntimeWires.Polygraph.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.Polygraph.Adjunction

public section

namespace Silmaril.RuntimeWires.Polygraph

open CategoryTheory

universe u v

/-- The functor that interprets every generator as effectful. -/
def allEffectfulFunctor : Polygraph.{u,v} ⥤ EffectfulPolygraph.{u,v} :=
  Proofs.allEffectful

/-- Proposition 5.2. Interpreting generators as effectful is left adjoint to forgetting
pure generators. -/
def allEffectfulAdjunction : allEffectfulFunctor.{u,v} ⊣ EffectfulPolygraph.forgetPure :=
  Proofs.allEffectfulAdjunction

end Silmaril.RuntimeWires.Polygraph
