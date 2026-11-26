module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Institution.Defs
public import Mathlib.CategoryTheory.IsoCat
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.ValidatedInstitution

/-! # A retraction of exact equation institutions on coherent models -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Inst Room)
open Morphism (SignatureMap)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

/-- Presenting the expanded SSA model recovers the validated algebra and
its chosen type model. The remaining fields are proofs. -/
@[simp] theorem validate_expand (A : ValidatedCaseAlgebra J P) :
    A.expand.validate J = A :=
  validate_expand_proof A

/-- Every coherent model is in the literal image of expansion. -/
@[simp] theorem expand_validate (K : CoherentRegionModel J P) :
    (K.validate J).expand = K :=
  ValidatedCaseAlgebra.expand_ofPresentation K K.caseAlgebra rfl

/-- Forgetting the chosen presentation has exactly the same literal object
image among LetCase algebras as the coherent SSA reduct. -/
theorem forgetValidation_range :
    Set.range (forgetValidation J P).obj =
      Set.range (CoherentRegionModel.caseAlgebra (J := J) (P := P)) :=
  forgetValidation_range_proof

/-- Between two chosen presentations, the only algebra arrows in the image
of the restriction are those induced by equality of the validated models. -/
theorem forgetValidation_map_iff {A B : (validatedRoom J P).Mod}
    (f : (forgetValidation J P).obj A ⟶ (forgetValidation J P).obj B) :
    (∃ h : A ⟶ B, (forgetValidation J P).map h = f) ↔
      ∃ e : A = B, f = eqToHom (congrArg (forgetValidation J P).obj e) :=
  forgetValidation_map_iff_proof f

section SignatureMaps

variable (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums]

@[simp] theorem validatedCorridor_id :
    validatedCorridor (J := J) (P := P) (Q := P) SignatureMap.id = 𝟙 (validatedRoom J P) :=
  validatedCorridor_id_proof

theorem validatedCorridor_comp :
    validatedCorridor (J := J) (h.comp g) = validatedCorridor g ≫ validatedCorridor h :=
  validatedCorridor_comp_proof g h

/-- Forgetting validation commutes with the existing LetCase signature map,
including the functor on algebra morphisms. -/
theorem restrictCase_natural :
    PresSig.inst.map (typeCaseHom g) ≫ restrictCaseCorridor J Q =
      restrictCaseCorridor J P ≫ validatedCorridor g :=
  restrictCase_natural_proof g

variable [FreydCategory.CentralUnit J]

theorem validatedReify_natural :
    validatedCorridor g ≫ validatedReifyCorridor J Q =
      validatedReifyCorridor J P ≫ ssaSignatureCorridor g :=
  validatedReify_natural_proof g

theorem validatedCompile_natural :
    ssaSignatureCorridor g ≫ validatedCompileCorridor J Q =
      validatedCompileCorridor J P ≫ validatedCorridor g :=
  validatedCompile_natural_proof g

end SignatureMaps

variable [FreydCategory.CentralUnit J]

/-- Restricting to validated models factors the original exact corridor. -/
theorem restrictCase_reify :
    restrictCaseCorridor J P ≫ validatedReifyCorridor J P = reifyCorridor J P :=
  restrictCase_reify_proof

/-- The LetCase round trip is the identity on exact equations and on model
functors. -/
theorem validatedReify_compile :
    validatedReifyCorridor J P ≫ validatedCompileCorridor J P = 𝟙 (validatedRoom J P) :=
  validatedReify_compile_proof

/-- The SSA round trip is the identity on the entire coherent model category. -/
theorem validatedCompile_reify_mod :
    (validatedCompileCorridor J P ≫ validatedReifyCorridor J P).mod = 𝟭 (ssaRoom J P).Mod :=
  validatedCompile_reify_mod_proof

/-- Reifying a compiled SSA sentence preserves its truth in every coherent
model, even when the exact structured code changes. -/
theorem reify_compile_sat (K : (ssaRoom J P).Mod) (e : SSAEquation P) :
    (ssaRoom J P).Sat K (reify (compile e)) ↔ (ssaRoom J P).Sat K e :=
  reify_compile_sat_proof K e

/-- On model categories the two corridor functors are inverse. The SSA side
is the whole discrete category of coherent region models. -/
noncomputable def validatedModelIso (P : InstrSig τ ε) :
    IsoCat (validatedRoom J P).Mod (ssaRoom J P).Mod where
  functor := (validatedCompileCorridor J P).mod
  inverse := (validatedReifyCorridor J P).mod
  unit_eq := (congrArg (fun f : validatedRoom J P ⟶ validatedRoom J P => f.mod)
    validatedReify_compile).symm
  counit_eq := validatedCompile_reify_mod

/-- The fixed points of the exact SSA sentence round trip are precisely the
image of reification. -/
theorem reify_compile_eq_iff (e : SSAEquation P) :
    reify (compile e) = e ↔ e ∈ Set.range (reify (P := P)) :=
  ⟨fun h => ⟨compile e, h⟩, by rintro ⟨φ, rfl⟩; rw [compile_reify]⟩

/-- Equational consequence on the validated class agrees with consequence
of reified equations in the coherent SSA room. -/
theorem validated_entails_reify_iff (Γ : Set (CaseEquation P)) (e : CaseEquation P) :
    (validatedRoom J P).Entails Γ e ↔ (ssaRoom J P).Entails (reify '' Γ) (reify e) := by
  let iso := validatedModelIso (J := J) P
  exact (validatedReifyCorridor J P).entails_map_iff
    (fun A => ⟨iso.functor.obj A, (Functor.congr_obj iso.unit_eq A).symm⟩) Γ e

variable (J)

/-- The exact LetCase institution restricted to validated algebras. -/
noncomputable def validatedTypeInst : TypeSignature ⥤ Room.{0, 0, 1} where
  obj P := validatedRoom J P.prim
  map f := validatedCorridor f.signatureMap
  map_id _ := validatedCorridor_id
  map_comp f g := validatedCorridor_comp f.signatureMap g.signatureMap

/-- The validated LetCase institution with the original type-changing signatures. -/
noncomputable def validatedCaseInstitution : Inst.{1, 0, 0, 0, 1} :=
  ⟨TypeSignature, validatedTypeInst J⟩

/-- Restriction from the original LetCase institution, with the original
sentence action and the forgetful model functor. -/
noncomputable def restrictCaseNatural : letCaseTypeInst ⟶ validatedTypeInst J where
  app P := restrictCaseCorridor J P.prim
  naturality {_ _} f := restrictCase_natural f.signatureMap

/-- Reification is natural over the full type-changing signature category. -/
noncomputable def validatedReifyNatural : validatedTypeInst J ⟶ ssaTypeInst J where
  app P := validatedReifyCorridor J P.prim
  naturality {_ _} f := validatedReify_natural f.signatureMap

/-- Compilation is natural over the full type-changing signature category. -/
noncomputable def validatedCompileNatural : ssaTypeInst J ⟶ validatedTypeInst J where
  app P := validatedCompileCorridor J P.prim
  naturality {_ _} f := validatedCompile_natural f.signatureMap

/-- The reification comorphism over the identity on signatures. -/
noncomputable def validatedReifyComorphism :
    Inst.CoHom (validatedCaseInstitution J) (ssaTypeInstitution J) where
  Φ := 𝟭 TypeSignature
  ρ := validatedReifyNatural J ≫ (Functor.leftUnitor (ssaTypeInst J)).inv

/-- The compilation comorphism over the identity on signatures. -/
noncomputable def validatedCompileComorphism :
    Inst.CoHom (ssaTypeInstitution J) (validatedCaseInstitution J) where
  Φ := 𝟭 TypeSignature
  ρ := validatedCompileNatural J ≫ (Functor.leftUnitor (validatedTypeInst J)).inv

/-- Reification followed by compilation retracts the validated institution
as a diagram of rooms. -/
theorem validatedReify_compile_natural :
    validatedReifyNatural J ≫ validatedCompileNatural J = 𝟙 (validatedTypeInst J) := by
  exact NatTrans.ext (funext fun P => validatedReify_compile (J := J) (P := P.prim))

/-- The two comorphisms give a retraction over the same signature category. -/
theorem validatedReify_compile_comorphism :
    (validatedReifyComorphism J).comp (validatedCompileComorphism J) =
      Inst.CoHom.id (validatedCaseInstitution J) :=
  Inst.CoHom.ext rfl (NatTrans.ext (funext fun (P : TypeSignature) =>
    validatedReify_compile (J := J) (P := P.prim)))

/-- The natural reification against all LetCase algebras factors through
the validated restriction. -/
theorem restrictCase_reify_natural :
    restrictCaseNatural J ≫ validatedReifyNatural J = typeReifyNatural J := by
  exact NatTrans.ext (funext fun P => restrictCase_reify (J := J) (P := P.prim))

end Silmaril.Isotope.Institution.Acyclic
