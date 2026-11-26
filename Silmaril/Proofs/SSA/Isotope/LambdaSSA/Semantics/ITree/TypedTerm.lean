module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs

/-! # Erasure of exact categorical term denotations in the weak ITree model -/

public section

universe u v q r

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Agreement
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel TypeModel TyDen)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (typeJ bind_of pair_of caseWithContext_of comp_map_of)
open Silmaril.Elgot.ITree

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {κ : Type (v + 1)} [AtomValues κ]
  {E : Type v → Type v} {Φ : Type q} [HasTy Φ (Ty κ)]
  [HasEff Φ Bool]

attribute [local instance] typeModel

variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)] (raw : Primitive E Φ (Sigma (AtomValues.carrier (κ := κ))))

local notation "V" => AtomValues.carrier (κ := κ)
local notation "TM" => ModelTree E
local notation "J" => typeJ (m := TM)
local notation "T" => Categorical.ofMonadicTypeModel (τ := Ty κ)

attribute [local instance] categoricalInstructions

omit [HasTy Φ (Ty κ)] [HasEff Φ Bool] [InstructionModel Φ (Ty κ) Bool TM] in
theorem encodesEnv_extend {Γ : VCtx (Ty κ)} {ρ : Monadic.Env Γ} {env : Env (Sigma V)}
    (h : EncodesEnv ρ env) {A : Ty κ} (a : Ty.denote V A) :
    EncodesEnv (Γ := A :: Γ) (ρ, a) (extend env (encodeValue V A a)) := by
  intro i B hi
  cases i with
  | zero =>
    have eq : A = B := Option.some.inj hi
    subst B
    rfl
  | succ i => exact h i B hi

theorem termDenotes_tree
    (compat : Compatible (κ' := κ) ⟨fun f x => InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := TM) f x⟩ raw)
    {Γ : VCtx (Ty κ)} {t : Tm Φ} {A : Ty κ} {ht : Tm.HasType Γ t A}
    {f : (J).obj (Categorical.ctxObj T Γ) ⟶ (J).obj ((T).obj A)}
    (d : Categorical.Denotes J T ht f)
    (ρ : Monadic.Env Γ) (env : Env (Sigma V)) (h : EncodesEnv ρ env) :
    ((show TM (Ty.denote V A) from f.of (envToCategorical ρ)) >>= fun a => pure (encodeValue V A a)) = term raw env t := by
  induction d generalizing env with
  | var hi =>
    rw [lookup_agrees]
    simp only [pure_bind, term, h _ _ hi]
  | op d ih =>
    rw [Kleisli.Type.comp_of_eq_kleisliRight]
    change ((_ >>= InstructionModel.denote (ε := Bool) _) >>= _) = _
    rw [term, ← ih ρ env h, bind_assoc, bind_assoc]
    exact bind_congr (fun a => by rw [pure_bind]; exact (compat _ a).symm)
  | let₁ da db iha ihb =>
    rw [bind_of]
    simp only [Bind.kleisliRight, term, ← iha ρ env h, bind_assoc, pure_bind]
    exact bind_congr (fun a => ihb (ρ, a) _ (encodesEnv_extend h a))
  | pair da db iha ihb =>
    rw [Kleisli.Type.comp_of_eq_kleisliRight]
    simp only [Bind.kleisliRight]
    erw [pair_of]
    simp only [Bind.kleisliRight, term, ← iha ρ env h, ← ihb ρ env h,
      bind_assoc, mapTree_of, pure_bind]
    rfl
  | unit =>
    change (pure (PUnit.unit : Ty.denote V .unit) >>= _) = _
    rw [pure_bind]
    rfl
  | let₂ da db iha ihb =>
    rename_i Γ t A B ha fa r C hb fb
    rw [bind_of]
    simp only [Bind.kleisliRight, term, ← iha ρ env h, bind_assoc, pure_bind]
    apply bind_congr
    rintro ⟨a, b⟩
    rw [← Category.assoc, ← Functor.map_comp, Kleisli.Type.comp_of_eq_kleisliRight]
    change (((pure (envToCategorical (Γ := B :: A :: Γ) ((ρ, a), b)) : TM _) >>= fun z =>
      (show TM _ from fb.of z)) >>= _) = _
    rw [pure_bind]
    exact ihb ((ρ, a), b) _ (encodesEnv_extend (encodesEnv_extend h a) b)
  | inl da iha =>
    rename_i Γ t A ht fa B
    rw [Kleisli.Type.comp_of_eq_kleisliRight]
    simp only [Bind.kleisliRight, term, ← iha ρ env h, bind_assoc, pure_bind]
    apply bind_congr
    intro a
    let tagged := ((T).coprodIso A B).inv ((coprod.inl : (T).obj A ⟶ (T).obj A ⨿ (T).obj B) a)
    change ((pure tagged : TM _) >>= _) = _
    rw [pure_bind]
    change pure (encodeValue V _ (((T).coprodIso _ _).inv ((coprod.inl : (T).obj A ⟶ (T).obj A ⨿ (T).obj B) a))) = _
    have tag : ((T).coprodIso _ _).inv ((coprod.inl : (T).obj A ⟶ (T).obj A ⨿ (T).obj B) a) = Sum.inl a := by
      apply (TypeModel.coprodEquiv _ _).injective
      rw [← coprod_hom_agrees]
      rw [Iso.inv_hom_id_apply]
      exact ConcreteCategory.congr_hom (Types.binaryCoproductIso_inl_comp_hom ((T).obj A) ((T).obj B)) a
    rw [tag]
    rfl
  | inr da iha =>
    rename_i Γ t B ht fb A
    rw [Kleisli.Type.comp_of_eq_kleisliRight]
    simp only [Bind.kleisliRight, term, ← iha ρ env h, bind_assoc, pure_bind]
    apply bind_congr
    intro b
    let tagged := ((T).coprodIso A B).inv ((coprod.inr : (T).obj B ⟶ (T).obj A ⨿ (T).obj B) b)
    change ((pure tagged : TM _) >>= _) = _
    rw [pure_bind]
    change pure (encodeValue V _ (((T).coprodIso _ _).inv ((coprod.inr : (T).obj B ⟶ (T).obj A ⨿ (T).obj B) b))) = _
    have tag : ((T).coprodIso _ _).inv ((coprod.inr : (T).obj B ⟶ (T).obj A ⨿ (T).obj B) b) = Sum.inr b := by
      apply (TypeModel.coprodEquiv _ _).injective
      rw [← coprod_hom_agrees]
      rw [Iso.inv_hom_id_apply]
      exact ConcreteCategory.congr_hom (Types.binaryCoproductIso_inr_comp_hom ((T).obj A) ((T).obj B)) b
    rw [tag]
    rfl
  | case de dl dr ihe ihl ihr =>
    rw [caseWithContext_of]
    simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight, term, ← ihe ρ env h, bind_assoc, mapTree_of, pure_bind]
    apply bind_congr
    intro ab
    rw [coprod_hom_agrees]
    rcases ab with a | b
    · exact ihl (ρ, a) _ (encodesEnv_extend h a)
    · exact ihr (ρ, b) _ (encodesEnv_extend h b)
  | abort da iha =>
    rw [Kleisli.Type.comp_of_eq_kleisliRight]
    simp only [Bind.kleisliRight, term, ← iha ρ env h, bind_assoc, pure_bind]
    exact bind_congr (fun z => (TypeModel.emptyEquiv z).elim)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed
