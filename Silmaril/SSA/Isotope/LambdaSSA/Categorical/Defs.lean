module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

/-! # Categorical denotation of typed λSSA

An expression denotes an arrow out of the product of its variable types.
A region denotes an arrow into the coproduct of its exit argument types.
A nonempty CFG dispatches through a coproduct of its internal labels and uses
contextual Elgot iteration while carrying the surrounding variable context.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (bind pair caseWithContext contextualLoop)

section ValueContext

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V] {τ : Type u₃} [TypeFormers τ]

/-- Interpretation of a newest-first SSA value context.  The newest value is
the right tensor factor, matching the context convention of lambda-iter. -/
def ctxObj (M : TypeModel τ V) : VCtx τ → V
  | [] => 𝟙_ V
  | A :: Γ => ctxObj M Γ ⊗ M.obj A

/-- A typed de Bruijn lookup interpreted as a Cartesian projection. -/
noncomputable def lookup (M : TypeModel τ V) : {Γ : VCtx τ} →
    (i : Nat) → {A : τ} → At Γ i A → (ctxObj M Γ ⟶ M.obj A)
  | [], _, _, h => by simp [At] at h
  | _ :: _, 0, _, h => by
      simp [At] at h
      subst_vars
      exact CartesianMonoidalCategory.snd _ _
  | _ :: _, i + 1, _, h =>
      CartesianMonoidalCategory.fst _ _ ≫ lookup M i h

/-- Reassociate an environment extended by a pair into the two newest SSA
slots.  Since contexts are newest-first, `B` is the head after destructuring. -/
def ctxPairIso (M : TypeModel τ V) (Γ : VCtx τ) (A B : τ) :
    ctxObj M Γ ⊗ (M.obj A ⊗ M.obj B) ≅ ctxObj M (B :: A :: Γ) :=
  (α_ (ctxObj M Γ) (M.obj A) (M.obj B)).symm

variable (M : TypeModel τ V) {n : Nat}

/-- A label context is interpreted as the finite coproduct of its parameter
types, as in the paper semantics. -/
noncomputable def labelObj (M : TypeModel τ V) (L : LCtx τ) : V :=
  ∐ fun i : Fin L.length => M.obj (L.get i)

/-- The coproduct injection selected by typed label lookup evidence. -/
noncomputable def labelInject (M : TypeModel τ V) {L : LCtx τ}
    (i : Nat) {A : τ} (h : At L i A) : M.obj A ⟶ labelObj M L := by
  have hi : i < L.length := by
    have hh := h
    change L[i]? = some A at hh
    rw [List.getElem?_eq_some_iff] at hh
    exact hh.1
  let j : Fin L.length := ⟨i, hi⟩
  have hj : L.get j = A := by
    have : L[i]? = some (L.get j) := by simp [j]
    rw [h] at this
    exact Option.some.inj this.symm
  exact eqToHom (congrArg M.obj hj.symm) ≫
    Sigma.ι (fun k : Fin L.length => M.obj (L.get k)) j

/-- The internal labels indexed by their arity, before converting through the
list representation used by the surface typing judgment. -/
noncomputable def finiteLabelObj (R : Fin n → τ) : V :=
  ∐ fun i : Fin n => M.obj (R i)

noncomputable def finiteLabelInject (R : Fin n → τ) (i : Fin n) :
    M.obj (R i) ⟶ finiteLabelObj M R :=
  Limits.Sigma.ι (fun j : Fin n => M.obj (R j)) i

/-- Forget that a finite label family was materialized as `List.ofFn`. -/
noncomputable def labelObjToFinite (R : Fin n → τ) :
    labelObj M (List.ofFn R) ⟶ finiteLabelObj M R :=
  Limits.Sigma.desc fun j => by
    let i : Fin n := ⟨j, by simpa using j.isLt⟩
    have h : (List.ofFn R).get j = R i := by simp [i]
    exact eqToHom (congrArg M.obj h) ≫ finiteLabelInject M R i

noncomputable def labelAppendRoute (R L : LCtx τ)
    (i : Fin (R ++ L).length) :
    M.obj ((R ++ L).get i) ⟶ labelObj M L ⨿ labelObj M R := by
  by_cases hi : i.val < R.length
  · exact labelInject M i.val (by
      simp only [At]
      simp [hi]) ≫ coprod.inr
  · let j := i.val - R.length
    exact labelInject M j (by
      change L[j]? = some (R ++ L)[i.val]
      have ht : (R ++ L)[i.val]? = some (R ++ L)[i.val] := by simp
      rw [List.getElem?_append_right (by omega)] at ht
      simpa [j] using ht) ≫ coprod.inl

/-- Separate external from locally bound labels in an appended label context.
The local labels occur first because label contexts use de Bruijn order. -/
noncomputable def labelAppendSplit (R L : LCtx τ) :
    labelObj M (R ++ L) ⟶ labelObj M L ⨿ labelObj M R :=
  Limits.Sigma.desc (labelAppendRoute M R L)

end ValueContext

section Term

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The graph of denotation.  Typing is a `Prop`, so Lean cannot eliminate a
typing derivation directly into a hom-set.  The relation records the constructor equations in `Prop`. -/
inductive Denotes : {Γ : VCtx τ} → {t : Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → (J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)) → Prop where
  | var (h : At Γ i A) : Denotes (.var h) (J.map (lookup M i h))
  | op (dha : Denotes ha fa) :
      Denotes (.op ha) (fa ≫ InstructionModel.denote _)
  | let₁ (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.let₁ ha hb) (bind J fa fb)
  | pair (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.pair ha hb)
        (pair J fa fb ≫ J.map (M.productIso _ _).inv)
  | unit : Denotes (.unit (Γ := Γ))
      (J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv))
  | let₂ (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.let₂ ha hb) (bind J fa (
        J.map ((𝟙 _) ⊗ₘ (M.productIso _ _).hom) ≫
          J.map (ctxPairIso M _ _ _).hom ≫ fb))
  | inl (dha : Denotes ha fa) : Denotes (.inl (B := B) ha)
      (fa ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv))
  | inr (dhb : Denotes hb fb) : Denotes (.inr (A := A) hb)
      (fb ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv))
  | case (dhe : Denotes he fe) (dhl : Denotes hl fl)
      (dhr : Denotes hr fr) : Denotes (.case he hl hr)
        (caseWithContext J (fe ≫ J.map (M.coprodIso _ _).hom) fl fr)
  | abort (dha : Denotes ha fa) : Denotes (.abort (A := A) ha) (fa ≫ J.map (M.emptyIsInitial.to (M.obj A)))

/-- Coherence identifies all structural expression denotations at a fixed typed term. -/
class TypingCoherent : Prop where
  denotes_eq {Γ : VCtx τ} {t : Tm Φ} {A : τ} {h : Tm.HasType Γ t A}
      {f g : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} :
    Denotes J M h f → Denotes J M h g → f = g

end Term

section Region

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- A collective block arrow is characterized by its restriction to every
local-label summand, with the read-only SSA context carried on the left. -/
structure CollectiveDenotes (Γ : VCtx τ) {n : Nat} (R : Fin n → τ) (L : LCtx τ)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
      J.obj (labelObj M (List.ofFn R ++ L)))
    (f : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶
      J.obj (labelObj M (List.ofFn R ++ L))) : Prop where
  restrict (i : Fin n) :
    J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i) ≫ f = block i

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Structural denotation of a typed region, including nested CFG binders.
The zero-block rule delegates straight to the entry. A nonempty CFG splits
outward jumps from local jumps and iterates only the local dispatcher. -/
inductive RegionDenotes : {Γ : VCtx τ} → {r : Region Φ} → {L : LCtx τ} →
    Region.HasType Γ r L → (J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)) → Prop where
  | br (dt : Denotes J M ha fa) :
      RegionDenotes (.br h ha) (fa ≫ J.map (labelInject M _ h))
  | case (de : Denotes J M he fe)
      (dl : RegionDenotes hl fl) (dr : RegionDenotes hr fr) :
      RegionDenotes (.case he hl hr)
        (caseWithContext J (fe ≫ J.map (M.coprodIso _ _).hom) fl fr)
  | let₁ (da : Denotes J M ha fa) (db : RegionDenotes hb fb) :
      RegionDenotes (.let₁ ha hb) (bind J fa fb)
  | let₂ (da : Denotes J M ha fa) (db : RegionDenotes hb fb) :
      RegionDenotes (.let₂ ha hb) (bind J fa (
        J.map ((𝟙 _) ⊗ₘ (M.productIso _ _).hom) ≫
          J.map (ctxPairIso M _ _ _).hom ≫ fb))
  | cfgZero {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
      {R : Fin 0 → τ} {blocks : Fin 0 → Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
      (de : RegionDenotes he fe) :
      RegionDenotes (.cfg R he hb) fe
  | cfg {n : Nat} {R : Fin (n + 1) → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : Region Φ} {blocks : Fin (n + 1) → Region Φ}
      (he : Region.HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
      {fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
      {fb : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
        J.obj (labelObj M (List.ofFn R ++ L))}
      {collective : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶
        J.obj (labelObj M (List.ofFn R ++ L))}
      (de : RegionDenotes he fe)
      (db : ∀ i, RegionDenotes (hb i) (fb i))
      (dc : CollectiveDenotes J M Γ R L fb collective) :
      RegionDenotes (.cfg R he hb) (caseWithContext J
        (fe ≫ J.map (labelAppendSplit M (List.ofFn R) L))
        (J.map (CartesianMonoidalCategory.snd _ _))
        (contextualLoop J
          (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelObjToFinite M R) ≫
            collective ≫ J.map (labelAppendSplit M (List.ofFn R) L))))

/-- Optional coherence for the relational region semantics. -/
class RegionTypingCoherent : Prop where
  denotes_eq {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
      {h : Region.HasType Γ r L}
      {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} :
      RegionDenotes J M h f → RegionDenotes J M h g → f = g

end Region

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
