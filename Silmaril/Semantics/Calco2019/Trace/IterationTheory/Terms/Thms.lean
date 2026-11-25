module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Terms.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationTerms

/-! # Copower coherence for the interpretation of iteration terms -/

@[expose] public section

universe u v w

namespace Silmaril.Calco2019.IterationTheory

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X : K} (C : FiniteCopowers X)
  {I J E : Arity}

namespace FiniteCopowers

/-- Splitting the index set and rejoining acts as the identity on the copower. -/
theorem split_join (P : Coproducts K) (I J : Arity) :
    C.split P I J ≫ C.join P I J = 𝟙 _ :=
  Proofs.IterationTerms.split_join C P I J

/-- Joining and splitting acts as the identity on the chosen binary coproduct. -/
theorem join_split (P : Coproducts K) (I J : Arity) :
    C.join P I J ≫ C.split P I J = 𝟙 _ :=
  Proofs.IterationTerms.join_split C P I J

/-- The selected binary coproduct is canonically the copower on the disjoint union. -/
def sumIso (P : Coproducts K) (I J : Arity) :
    (C.cofan (I.sum J)).pt ≅ P.sum (C.cofan I).pt (C.cofan J).pt where
  hom := C.split P I J
  inv := C.join P I J
  hom_inv_id := C.split_join P I J
  inv_hom_id := C.join_split P I J

@[reassoc (attr := simp)]
theorem inj_inl_split (i : I) :
    (C.cofan (I.sum J)).inj (.inl i) ≫ C.split P I J = (C.cofan I).inj i ≫ P.inl :=
  Cofan.IsColimit.fac (C.colimit (I.sum J)) _ (.inl i)

@[reassoc (attr := simp)]
theorem inj_inr_split (j : J) :
    (C.cofan (I.sum J)).inj (.inr j) ≫ C.split P I J = (C.cofan J).inj j ≫ P.inr :=
  Cofan.IsColimit.fac (C.colimit (I.sum J)) _ (.inr j)

end FiniteCopowers

namespace Term

variable {σ : Signature.{w}} (F : (Guardedness.greatest P).Fixpoints)
  (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt)

/-- The generator's sole input component recovers the assigned operation. -/
@[simp]
theorem evaluate_generator (a : σ.Symbol) (i : Arity.one) :
    (C.cofan Arity.one).inj i ≫ evaluate C F op (.generator a) = op a :=
  Cofan.IsColimit.fac (C.colimit Arity.one) _ i

/-- Pairing evaluates componentwise on an input from the first summand. -/
@[simp]
theorem evaluate_pair_inl (f : Term σ I E) (g : Term σ J E) (i : I) :
    (C.cofan (I.sum J)).inj (.inl i) ≫ evaluate C F op (.pair f g) =
      (C.cofan I).inj i ≫ evaluate C F op f := by
  rw [evaluate, FiniteCopowers.inj_inl_split_assoc, P.inl_desc]

/-- Pairing evaluates componentwise on an input from the second summand. -/
@[simp]
theorem evaluate_pair_inr (f : Term σ I E) (g : Term σ J E) (j : J) :
    (C.cofan (I.sum J)).inj (.inr j) ≫ evaluate C F op (.pair f g) =
      (C.cofan J).inj j ≫ evaluate C F op g := by
  rw [evaluate, FiniteCopowers.inj_inr_split_assoc, P.inr_desc]

end Term

end Silmaril.Calco2019.IterationTheory
