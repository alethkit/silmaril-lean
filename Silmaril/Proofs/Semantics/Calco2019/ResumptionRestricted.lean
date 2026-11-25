module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Restricted.Defs
public import Silmaril.Semantics.Calco2019.VacuousThms

public section

universe u v

namespace Silmaril.Calco2019.Exception.Proofs

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)

theorem free_restricted (W : ObjectProperty (GuardedElgotMonad P))
    (base : W T) (res : W ((parametrizedElgot T H).resumptionElgotMonad R))
    (S : W.FullSubcategory) (σ : GuardedTransformation H S.obj)
    (h : (⟨T, base⟩ : W.FullSubcategory) ⟶ S) :
    ∃! k : (⟨(parametrizedElgot T H).resumptionElgotMonad R, res⟩ : W.FullSubcategory) ⟶ S,
      suspension T H R ≫ k.hom.hom.toNatTrans = σ.val ∧ baseEmbedding T H R ≫ k.hom = h.hom := by
  obtain ⟨k, hk, unique⟩ := resumption_free R S.obj σ h.hom
  refine ⟨ObjectProperty.homMk k, ⟨?_, hk.2⟩, ?_⟩
  · exact ((guardedBimodule_post (resumptionGenerator R) k).symm.trans
      (congrArg Subtype.val hk.1))
  · intro l hl
    apply ObjectProperty.hom_ext
    apply unique
    refine ⟨?_, hl.2⟩
    apply Subtype.ext
    exact (guardedBimodule_post (resumptionGenerator R) l.hom).trans hl.1

theorem identityResumption_freeOn
    (R₀ : FinalResumptions (parametrizedElgot (guardedIdentity P) H).toParametrizedMonad)
    (S : GuardedIterativeElgot P) (σ : GuardedTransformation H S.obj) :
    ∃! k : (⟨(parametrizedElgot (guardedIdentity P) H).resumptionElgotMonad R₀,
        resumption_iterative (guardedIdentity P) H R₀ (Guardedness.vacuous_iterative)⟩ :
        GuardedIterativeElgot P) ⟶ S,
      suspension (guardedIdentity P) H R₀ ≫ k.hom.hom.toNatTrans = σ.val := by
  obtain ⟨k, hk, unique⟩ := resumption_freeObject (P := P) H R₀ S.obj σ
  refine ⟨ObjectProperty.homMk k, ?_, ?_⟩
  · exact ((guardedBimodule_post (resumptionGenerator R₀) k).symm.trans
      (congrArg Subtype.val hk))
  · intro l hl
    apply ObjectProperty.hom_ext
    apply unique
    apply Subtype.ext
    exact (guardedBimodule_post (resumptionGenerator R₀) l.hom).trans hl

end Silmaril.Calco2019.Exception.Proofs
