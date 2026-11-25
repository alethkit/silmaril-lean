module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Completeness.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationCompleteness

/-! # Equational completeness of Conway and the commutative identities -/

public section

universe u v w

namespace Silmaril.Calco2019.IterationTheory.Term

open CategoryTheory

/-- The pointed path interpretation separates precisely the equations
valid in all standard pointed ω-cpo models. -/
theorem validInPointedDomains_iff_path {σ : Signature.{u}} {I E : Arity} (f g : Term σ I E) :
    f.ValidInPointedDomains g ↔ f.pathDenotation = g.pathDenotation :=
  Proofs.IterationCompleteness.pointed_iff_path f g

/-- Every equation valid in the standard models follows from the Conway
laws and commutative identities, in a category of any universe. -/
theorem equal_of_validInPointedDomains {K : Type u} [Category.{v} K]
    {P : Coproducts K} {X : K} (C : FiniteCopowers X) (F : (Guardedness.greatest P).Conway)
    (comm : C.CommutativeIdentities F.toFixpoints)
    {σ : Signature.{w}} {I E : Arity} (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt)
    {f g : Term σ I E} (valid : f.ValidInPointedDomains g) :
    f.evaluate C F.toFixpoints op = g.evaluate C F.toFixpoints op :=
  Proofs.IterationCompleteness.path_complete C F comm op f g ((validInPointedDomains_iff_path f g).mp valid)

/-- Conway with the commutative schema axiomatizes the equations of the
standard pointed-domain interpretation. The category universe in this
equivalence includes the standard model. -/
theorem validInPointedDomains_iff {σ : Signature.{u}} {I E : Arity} (f g : Term σ I E) :
    f.ValidInPointedDomains g ↔
      ∀ (K : Type (u + 1)) [Category.{u} K] (P : Coproducts K) (X : K)
        (C : FiniteCopowers X) (F : (Guardedness.greatest P).Conway)
        (_ : C.CommutativeIdentities F.toFixpoints)
        (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt),
        f.evaluate C F.toFixpoints op = g.evaluate C F.toFixpoints op := by
  refine ⟨fun h _ _ _ _ C F comm op => equal_of_validInPointedDomains C F comm op h, ?_⟩
  exact fun h D op => h _ PointedModel.coproducts D (PointedModel.copowers D)
    PointedModel.conway (PointedModel.commutative D) op

end Silmaril.Calco2019.IterationTheory.Term
