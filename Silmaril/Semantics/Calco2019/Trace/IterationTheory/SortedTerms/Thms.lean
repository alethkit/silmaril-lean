module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.SortedTerms.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationSortedTerms

/-! # Completeness for the many-sorted language of iteration theories -/

public section

universe u v w

namespace Silmaril.Calco2019.IterationTheory

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X : K}
  (C : FiniteCopowers X) (F : (Guardedness.greatest P).Fixpoints)

/-- Evaluation of a tuple agrees with evaluation at each input component. -/
theorem Term.tuple_component {σ : Signature.{w}} {E : Arity}
    (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt)
    {n : Nat} (ts : Fin n → Term σ Arity.one E) (i : Fin n) :
    (C.cofan (Fin n)).inj i ≫ (Term.tuple ts).evaluate C F op =
      (C.cofan Arity.one).inj PUnit.unit ≫ (ts i).evaluate C F op :=
  Proofs.IterationSortedTerms.tuple_component C F op ts i

namespace SortedTerm

variable {S : SortedSignature.{w}} {I E : Arity}

/-- The ranked translation of a generator recovers its assigned arrow. -/
@[simp]
theorem evaluate_generator (g : S.Assignment C) (a : S.Symbol) :
    (SortedTerm.generator a).evaluate C F g = g a :=
  Proofs.IterationSortedTerms.generator C F g a

/-- Every ranked assignment is obtained by taking the components of a
sorted assignment, so translation preserves and reflects standard validity. -/
theorem validInPointedDomains_iff_ranked (f g : SortedTerm S I E) :
    f.ValidInPointedDomains g ↔ f.ranked.ValidInPointedDomains g.ranked :=
  Proofs.IterationSortedTerms.ranked_valid f g

/-- Standard-valid equations with generators of arbitrary finite source and
target arity hold in every total Conway theory satisfying the commutative schema. -/
theorem equal_of_validInPointedDomains (T : (Guardedness.greatest P).Conway)
    (comm : C.CommutativeIdentities T.toFixpoints) (a : S.Assignment C)
    {f g : SortedTerm S I E} (valid : f.ValidInPointedDomains g) :
    f.evaluate C T.toFixpoints a = g.evaluate C T.toFixpoints a :=
  Term.equal_of_validInPointedDomains C T comm _ ((validInPointedDomains_iff_ranked f g).mp valid)

/-- The Conway and commutative identities axiomatize the valid equations of
the standard models for the many-sorted language. -/
theorem validInPointedDomains_iff (f g : SortedTerm S I E) :
    f.ValidInPointedDomains g ↔
      ∀ (K : Type (w + 1)) [Category.{w} K] (P : Coproducts K) (X : K)
        (C : FiniteCopowers X) (T : (Guardedness.greatest P).Conway)
        (_ : C.CommutativeIdentities T.toFixpoints) (a : S.Assignment C),
        f.evaluate C T.toFixpoints a = g.evaluate C T.toFixpoints a := by
  refine ⟨fun h _ _ _ _ C T comm a => equal_of_validInPointedDomains C T comm a h, ?_⟩
  exact fun h D a => h _ PointedModel.coproducts D (PointedModel.copowers D)
    PointedModel.conway (PointedModel.commutative D) a

end SortedTerm

end Silmaril.Calco2019.IterationTheory
