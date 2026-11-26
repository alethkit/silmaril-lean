module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Institution.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room Corridor)
open Morphism (SignatureMap)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

private theorem validated_ext {A B : ValidatedCaseAlgebra J P}
    (types : A.types = B.types) (algebra : A.algebra = B.algebra) : A = B := by
  cases A
  cases B
  cases types
  cases algebra
  rfl

theorem validate_expand_proof (A : ValidatedCaseAlgebra J P) :
    A.expand.validate J = A :=
  validated_ext rfl A.presentation

private theorem expand_validate (K : CoherentRegionModel J P) :
    (K.validate J).expand = K :=
  ValidatedCaseAlgebra.expand_ofPresentation K K.caseAlgebra rfl

private theorem expand_injective :
    Function.Injective (ValidatedCaseAlgebra.expand (J := J) (P := P)) :=
  Function.LeftInverse.injective validate_expand_proof

theorem forgetValidation_range_proof :
    Set.range (forgetValidation J P).obj =
      Set.range (CoherentRegionModel.caseAlgebra (J := J) (P := P)) := by
  ext B
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.fromShrinkHoms.as.expand, A.fromShrinkHoms.as.presentation⟩
  · rintro ⟨K, rfl⟩
    exact ⟨ShrinkHoms.toShrinkHoms (Discrete.mk (K.validate J)), rfl⟩

private theorem validatedModelFunctor_ext {D : Type*} [Category* D]
    {F G : (validatedRoom J P).Mod ⥤ D} (h : ∀ A, F.obj A = G.obj A) : F = G := by
  refine Functor.ext_of_iso (NatIso.ofComponents (fun A => eqToIso (h A)) ?_) h (fun _ => rfl)
  intro A B f
  obtain rfl := obj_ext_of_isDiscrete f
  have hf : f = 𝟙 A := Subsingleton.elim _ _
  subst f
  simp

theorem forgetValidation_map_iff_proof {A B : (validatedRoom J P).Mod}
    (f : (forgetValidation J P).obj A ⟶ (forgetValidation J P).obj B) :
    (∃ h : A ⟶ B, (forgetValidation J P).map h = f) ↔
      ∃ e : A = B, f = eqToHom (congrArg (forgetValidation J P).obj e) := by
  constructor
  · rintro ⟨h, rfl⟩
    let e := IsDiscrete.eq_of_hom h
    have eh : h = eqToHom e := Subsingleton.elim _ _
    exact ⟨e, (congrArg (forgetValidation J P).map eh).trans (eqToHom_map _ _)⟩
  · rintro ⟨e, rfl⟩
    exact ⟨eqToHom e, eqToHom_map _ _⟩

variable (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums]

private theorem reduct_id (A : ValidatedCaseAlgebra J P) :
    A.reduct SignatureMap.id = A :=
  expand_injective ((A.expand_reduct SignatureMap.id).trans (A.expand.pullback_id _))

private theorem reduct_comp (A : ValidatedCaseAlgebra J S) :
    A.reduct (h.comp g) = (A.reduct h).reduct g := by
  apply expand_injective
  calc
    (A.reduct (h.comp g)).expand = A.expand.pullback (h.comp g) _ := A.expand_reduct _
    _ = (A.expand.pullback h _).pullback g _ := A.expand.pullback_comp g h _ _ _
    _ = ((A.reduct h).expand).pullbackOfWitness g (regionWitnessPullback g (A.reduct h).expand) :=
      congrArg (fun K => K.pullbackOfWitness g (regionWitnessPullback g K)) (A.expand_reduct h).symm
    _ = ((A.reduct h).reduct g).expand := ((A.reduct h).expand_reduct g).symm

theorem validatedCorridor_id_proof :
    validatedCorridor (J := J) (P := P) (Q := P) SignatureMap.id = 𝟙 (validatedRoom J P) := by
  refine Room.hom_ext ?_ (validatedModelFunctor_ext fun A => ?_)
  · change (PresSig.inst.map (typeCaseHom (P := P) (Q := P) SignatureMap.id)).sen = id
    rw [typeCaseHom_id, CategoryTheory.Functor.map_id]
    rfl
  · exact congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk) (reduct_id A.fromShrinkHoms.as)

theorem validatedCorridor_comp_proof :
    validatedCorridor (J := J) (h.comp g) = validatedCorridor g ≫ validatedCorridor h := by
  refine Room.hom_ext ?_ (validatedModelFunctor_ext fun A => ?_)
  · change (PresSig.inst.map (typeCaseHom (h.comp g))).sen =
      (PresSig.inst.map (typeCaseHom h)).sen ∘ (PresSig.inst.map (typeCaseHom g)).sen
    rw [typeCaseHom_comp, Functor.map_comp]
    rfl
  · exact congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk) (reduct_comp g h A.fromShrinkHoms.as)

theorem restrictCase_natural_proof :
    PresSig.inst.map (typeCaseHom g) ≫ restrictCaseCorridor J Q =
      restrictCaseCorridor J P ≫ validatedCorridor g :=
  Room.hom_ext rfl (validatedModelFunctor_ext fun A => (A.fromShrinkHoms.as.reduct_algebra g).symm)

variable [FreydCategory.CentralUnit J]

theorem validatedReify_natural_proof :
    validatedCorridor g ≫ validatedReifyCorridor J Q =
      validatedReifyCorridor J P ≫ ssaSignatureCorridor g := by
  refine Room.hom_ext (funext fun e => ?_) (ssaModelFunctor_ext fun N => ?_)
  · exact (congrArg (reify (P := Q)) (typeCaseHom_translate g e)).trans (reify_mapCaseSignature g e)
  · apply congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
    apply expand_injective
    let K := N.fromShrinkHoms.as
    change ((K.validate J).reduct g).expand =
      ((K.pullbackOfWitness g (regionWitnessPullback g K)).validate J).expand
    simp only [ValidatedCaseAlgebra.expand_reduct, expand_validate]

theorem validatedCompile_natural_proof :
    ssaSignatureCorridor g ≫ validatedCompileCorridor J Q =
      validatedCompileCorridor J P ≫ validatedCorridor g := by
  refine Room.hom_ext (funext fun e => ?_) (validatedModelFunctor_ext fun A => ?_)
  · exact (compile_mapSSASignature g e).trans (typeCaseHom_translate g (compile e)).symm
  · exact congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk) (A.fromShrinkHoms.as.expand_reduct g).symm

theorem restrictCase_reify_proof :
    restrictCaseCorridor J P ≫ validatedReifyCorridor J P = reifyCorridor J P :=
  Room.hom_ext rfl (ssaModelFunctor_ext fun _ => rfl)

theorem validatedReify_compile_proof :
    validatedReifyCorridor J P ≫ validatedCompileCorridor J P = 𝟙 (validatedRoom J P) :=
  Room.hom_ext (funext compile_reify) (validatedModelFunctor_ext fun A =>
    congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk) (validate_expand_proof A.fromShrinkHoms.as))

theorem validatedCompile_reify_mod_proof :
    (validatedCompileCorridor J P ≫ validatedReifyCorridor J P).mod = 𝟭 (ssaRoom J P).Mod :=
  ssaModelFunctor_ext fun K =>
    congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk) (expand_validate K.fromShrinkHoms.as)

theorem reify_compile_sat_proof (K : (ssaRoom J P).Mod) (e : SSAEquation P) :
    (ssaRoom J P).Sat K (reify (compile e)) ↔ (ssaRoom J P).Sat K e :=
  (sat_reify_iff K.fromShrinkHoms.as (compile e)).trans (sat_compile_iff K.fromShrinkHoms.as e)

end Silmaril.Isotope.Institution.Acyclic
