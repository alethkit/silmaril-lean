module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Terms.Defs

public section

universe u v

namespace Silmaril.Calco2019.Proofs.IterationTerms

open CategoryTheory CategoryTheory.Limits IterationTheory

variable {K : Type u} [Category.{v} K] {X : K}
  (C : FiniteCopowers X) (P : Coproducts K) (I J : Arity)

private theorem split_inl (i : I) :
    (C.cofan (I.sum J)).inj (.inl i) ≫ C.split P I J = (C.cofan I).inj i ≫ P.inl :=
  Cofan.IsColimit.fac (C.colimit (I.sum J)) _ (.inl i)

private theorem split_inr (j : J) :
    (C.cofan (I.sum J)).inj (.inr j) ≫ C.split P I J = (C.cofan J).inj j ≫ P.inr :=
  Cofan.IsColimit.fac (C.colimit (I.sum J)) _ (.inr j)

theorem split_join : C.split P I J ≫ C.join P I J = 𝟙 _ := by
  unfold FiniteCopowers.join
  apply Cofan.IsColimit.hom_ext (C.colimit (I.sum J))
  rintro (i | j)
  · rw [← Category.assoc, split_inl, Category.assoc, P.inl_desc, C.reindex_inj, Category.comp_id]
  · rw [← Category.assoc, split_inr, Category.assoc, P.inr_desc, C.reindex_inj, Category.comp_id]

theorem join_split : C.join P I J ≫ C.split P I J = 𝟙 _ := by
  unfold FiniteCopowers.join
  apply P.hom_ext
  · rw [P.inl_desc_assoc, Category.comp_id]
    apply Cofan.IsColimit.hom_ext (C.colimit I)
    intro i
    rw [C.reindex_inj_assoc, split_inl]
  · rw [P.inr_desc_assoc, Category.comp_id]
    apply Cofan.IsColimit.hom_ext (C.colimit J)
    intro j
    rw [C.reindex_inj_assoc, split_inr]

end Silmaril.Calco2019.Proofs.IterationTerms
