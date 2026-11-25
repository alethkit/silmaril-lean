module

public import Silmaril.Semantics.RuntimeWires.Clique.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.Clique.Components

public section

namespace Silmaril.RuntimeWires.Clique

open CategoryTheory

universe u v w

/-- As in Definition 3.10, a clique morphism is uniquely specified by its component
at any selected input and output positions. -/
noncomputable def componentEquiv {C : Type u} [Category.{v} C] {I J : Type w}
    (A : Clique C I) (B : Clique C J) (a : I) (b : J) :
    Hom A B ≃ (A.obj a ⟶ B.obj b) :=
  Proofs.cliqueComponentEquiv a b

end Silmaril.RuntimeWires.Clique
