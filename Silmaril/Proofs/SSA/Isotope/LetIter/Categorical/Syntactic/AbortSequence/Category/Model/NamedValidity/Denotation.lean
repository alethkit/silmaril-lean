module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.NamedValidity.Closing.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.NamedValidity.Reopening
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.AbortSequence.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.LocallySmallValidity.Thms

open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasType AbortEquiv)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w r u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.NamedContext.DenotationProofs

open NamedContext

variable {ν : Type w} {τ : Type u} {Φ : Type v}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

section Environment

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [TypeFormers τ] (M : TypeModel τ V)

@[reassoc] theorem closeEnv_snoc (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n) (A : τ) :
    (envSnocIso M Γ β A).hom ≫ (closeEnvIso M Γ (.snoc β A)).hom =
      ((closeEnvIso M Γ β).hom ▷ M.obj A) ≫
        (envSnocIso M (Ctx.nil : Ctx Empty τ) (prepend (freeSlots Γ) β) A).hom := by
  simp [closeEnvIso]

@[reassoc] theorem closeEnv_pair (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    envPairHom M Γ β A B ≫ (closeEnvIso M Γ (.snoc (.snoc β A) B)).hom =
      ((closeEnvIso M Γ β).hom ▷ (M.obj A ⊗ M.obj B)) ≫
        envPairHom M (Ctx.nil : Ctx Empty τ) (prepend (freeSlots Γ) β) A B := by
  have expand (Δ : Ctx ν τ) {m : Nat} (δ : BoundCtx τ m) :
      envPairHom M Δ δ A B = (α_ (envObj M Δ δ) (M.obj A) (M.obj B)).inv ≫
        (envSnocIso M Δ δ A).hom ▷ M.obj B ≫ (envSnocIso M Δ (.snoc δ A) B).hom :=
    MonoidalCategory.pentagon_inv_hom_hom_hom_inv.symm
  have expandNil {m : Nat} (δ : BoundCtx τ m) :
      envPairHom M (Ctx.nil : Ctx Empty τ) δ A B =
      (α_ (envObj M (Ctx.nil : Ctx Empty τ) δ) (M.obj A) (M.obj B)).inv ≫
        (envSnocIso M (Ctx.nil : Ctx Empty τ) δ A).hom ▷ M.obj B ≫
        (envSnocIso M (Ctx.nil : Ctx Empty τ) (.snoc δ A) B).hom :=
    MonoidalCategory.pentagon_inv_hom_hom_hom_inv.symm
  rw [expand, expandNil]
  simp only [Category.assoc]
  erw [closeEnv_snoc M Γ (.snoc β A) B, ← MonoidalCategory.comp_whiskerRight_assoc,
    closeEnv_snoc M Γ β A, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.associator_inv_naturality_left_assoc, Category.assoc]
  rfl

open CategoryTheory.CartesianMonoidalCategory

@[reassoc] private theorem snoc_new (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n) (A : τ) :
    (envSnocIso M Γ β A).hom ≫ boundVar M (Γ := Γ) (β := .snoc β A) (0 : Fin (n + 1)) =
      snd (envObj M Γ β) (M.obj A) := by
  exact associator_hom_snd_snd _ _ _

@[reassoc] private theorem snoc_old (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n) (A : τ)
    (i : Fin n) :
    (envSnocIso M Γ β A).hom ≫ boundVar M (Γ := Γ) (β := .snoc β A) i.succ =
      fst (envObj M Γ β) (M.obj A) ≫ boundVar M (Γ := Γ) (β := β) i := by
  exact associator_hom_snd_fst_assoc _ _ _ _

@[reassoc] private theorem snoc_free [DecidableEq ν] (Γ : Ctx ν τ)
    {n : Nat} (β : BoundCtx τ n) (B : τ) (x : ν) {A : τ} (h : Γ.lookup x = some A) :
    (envSnocIso M Γ β B).hom ≫ freeLookup M (β := .snoc β B) x h =
      fst (envObj M Γ β) (M.obj B) ≫ freeLookup M (β := β) x h := by
  exact associator_hom_fst_assoc _ _ _ _

omit [HasFiniteCoproducts V] [TypeFormers τ] in
private theorem transport_fst {X Y X' : V} (h : X = X') :
    eqToHom (congrArg (fun R => R ⊗ Y) h) ≫ fst X' Y = fst X Y ≫ eqToHom h := by
  cases h
  simp

omit [HasFiniteCoproducts V] [TypeFormers τ] in
private theorem transport_snd {X Y X' : V} (h : X = X') :
    eqToHom (congrArg (fun R => R ⊗ Y) h) ≫ snd X' Y = snd X Y := by
  cases h
  simp

private theorem slot_projection [DecidableEq ν] (Γ : Ctx ν τ) (x : ν) {A : τ}
    (h : Γ.lookup x = some A) (i : Fin Γ.length) (hi : lookupSlot x Γ = some i)
    (e : (freeSlots Γ).get i = A) :
    eqToHom (freeSlots_obj M Γ) ≫ boundLookup M (β := freeSlots Γ) i ≫
        eqToHom (congrArg M.obj e) = ctxLookup M x h := by
  induction Γ with
  | nil => exact i.elim0
  | snoc Γ name B ih =>
    have tail (hj : (lookupSlot x Γ).map Fin.succ = some i) (hx : Γ.lookup x = some A)
        (he : ctxLookup M x h = fst _ _ ≫ ctxLookup M x hx) :
        eqToHom (freeSlots_obj M (.snoc Γ name B)) ≫
          boundLookup M (β := freeSlots (.snoc Γ name B)) i ≫
            eqToHom (congrArg M.obj e) = ctxLookup M x h := by
      cases hs : lookupSlot x Γ with
      | none => simp [hs] at hj
      | some j =>
        have eq : j.succ = i := Option.some.inj (by simpa only [hs, Option.map_some] using hj)
        subst i
        rw [he, ← ih hx j hs e]
        simp only [freeSlots, boundLookup, Fin.cases_succ, Category.assoc]
        rw [← Category.assoc]
        exact congrArg (fun f => f ≫ boundLookup M j ≫ eqToHom (congrArg M.obj e))
          (transport_fst (Y := M.obj B) (freeSlots_obj M Γ)) |>.trans (Category.assoc _ _ _)
    cases name with
    | none => exact tail hi h (by rw [ctxLookup])
    | some y =>
      by_cases hxy : x = y
      · subst y
        have ei : (0 : Fin (Γ.length + 1)) = i :=
          Option.some.inj (by simpa [lookupSlot] using hi)
        subst i
        have hBA : B = A := Option.some.inj (by simpa [Ctx.lookup] using h)
        subst A
        simp only [freeSlots, boundLookup, Fin.cases_zero, eqToHom_refl, Category.comp_id, ctxLookup]
        exact transport_snd (Y := M.obj B) (freeSlots_obj M Γ)
      · exact tail (by simpa only [lookupSlot, ite_eq_right hxy] using hi)
          (by simpa only [Ctx.lookup, ite_eq_right hxy] using h)
          (by simp [ctxLookup, hxy])

/-- Closing preserves the projection of each original bound index. -/
public theorem closeEnv_bound (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n) (i : Fin n) :
    (closeEnvIso M Γ β).hom ≫
        boundVar M (Γ := (Ctx.nil : Ctx Empty τ)) (β := prepend (freeSlots Γ) β)
          (boundIndex Γ.length i) ≫
        eqToHom (congrArg M.obj (prepend_get_bound (freeSlots Γ) β i)) =
      boundVar M (Γ := Γ) (β := β) i := by
  induction β with
  | nil => exact i.elim0
  | snoc β A ih =>
    apply (cancel_epi (envSnocIso M Γ β A).hom).mp
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [boundIndex, Fin.cases_zero, eqToHom_refl, Category.comp_id]
      rw [closeEnv_snoc_assoc, snoc_new, snoc_new]
      exact whiskerRight_snd _ _
    · simp only [boundIndex, Fin.cases_succ]
      rw [closeEnv_snoc_assoc, snoc_old_assoc, snoc_old]
      simp only [whiskerRight_fst_assoc, ih]

/-- Closing preserves lookup of each free name at the slot selected by native lookup. -/
public theorem closeEnv_free [DecidableEq ν] (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n)
    (x : ν) {A : τ} (h : Γ.lookup x = some A) (i : Fin Γ.length)
    (hi : lookupSlot x Γ = some i) (e : (freeSlots Γ).get i = A) :
    (closeEnvIso M Γ β).hom ≫
        boundVar M (Γ := (Ctx.nil : Ctx Empty τ)) (β := prepend (freeSlots Γ) β)
          (freeIndex i n) ≫
        eqToHom (congrArg M.obj ((prepend_get_free (freeSlots Γ) β i).trans e)) =
      freeLookup M (β := β) x h := by
  induction β with
  | nil =>
    simp only [closeEnvIso, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, boundVar, prepend,
      freeIndex, Category.assoc, ctxObj, leftUnitor_inv_snd_assoc, freeLookup, boundObj]
    rw [rightUnitor_hom, slot_projection M Γ x h i hi e]
  | snoc β B ih =>
    apply (cancel_epi (envSnocIso M Γ β B).hom).mp
    simp only [freeIndex]
    rw [closeEnv_snoc_assoc, snoc_old_assoc, snoc_free]
    simp only [whiskerRight_fst_assoc, ih]

end Environment

section Denotation

open CategoryTheory.CartesianMonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)

variable [DecidableEq ν] [TypeFormers τ] [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

private theorem denote_of_bound {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) (i : Fin n) (ht : t = .bv i) (e : β.get i = A) :
    denote J M d = J.map (boundVar M (Γ := Γ) (β := β) i ≫ eqToHom (congrArg M.obj e)) := by
  subst t
  cases d
  simp only [denote, eqToHom_refl, Category.comp_id]

private theorem denote_close_free {n : Nat} {β : BoundCtx τ n} {x : ν} {A : τ}
    (h : Γ.lookup x = some A) :
    denote J M (Derivation.fv (Φ := Φ) (β := β) h) =
      J.map (closeEnvIso M Γ β).hom ≫
        denote J M (closeDerivation (Derivation.fv (Φ := Φ) (β := β) h)) := by
  have slot := (lookupSlot_eq_lookup x Γ).trans h
  cases hs : lookupSlot x Γ with
  | none => simp [hs] at slot
  | some i =>
    have e : (freeSlots Γ).get i = A := Option.some.inj (by simpa [hs] using slot)
    have ht : closeTm (Φ := Φ) Γ (.fv (n := n) x) = .bv (freeIndex i n) := by
      simp only [closeTm, hs]
    rw [denote, denote_of_bound J M _ _ ht ((prepend_get_free (freeSlots Γ) β i).trans e),
      ← J.map_comp, closeEnv_free M Γ β x h i hs e]

private theorem denote_close_bound {n : Nat} (β : BoundCtx τ n) (i : Fin n) :
    denote J M (Derivation.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := i)) =
      J.map (closeEnvIso M Γ β).hom ≫
        denote J M (closeDerivation (Derivation.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := i))) := by
  have ht : closeTm (Φ := Φ) Γ (.bv i) = .bv (boundIndex Γ.length i) := rfl
  rw [denote, denote_of_bound J M _ _ ht (prepend_get_bound (freeSlots Γ) β i),
    ← J.map_comp, closeEnv_bound M Γ β i]

/-- Closing preserves denotation after the canonical change of environment. -/
public theorem denote_close
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    denote J M d = J.map ((closeEnvIso M Γ β).hom) ≫ denote J M (closeDerivation d) := by
  induction d with
  | fv h => exact denote_close_free J M h
  | @bv _ β i => exact denote_close_bound J M β i
  | unit =>
    simp only [closeDerivation, denote, ← J.map_comp, comp_toUnit_assoc]
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [closeDerivation, denote, ih, Category.assoc]
  | pair _ _ ih₁ ih₂ =>
    simp only [closeDerivation, denote, ih₁, ih₂, pair_pre_map, Category.assoc]
  | let₁ _ _ ih₁ ih₂ =>
    simp only [closeDerivation, denote, ih₁, ih₂]
    erw [← J.map_comp_assoc, closeEnv_snoc, J.map_comp_assoc, bind_pre_map]
  | @let₂ _ β _ _ A B _ _ _ ih₁ ih₂ =>
    simp only [closeDerivation, denote, ih₁, ih₂, MonoidalCategory.id_tensorHom]
    have exchange : (envObj M Γ β ◁ (M.productIso A B).hom) ≫
        ((closeEnvIso M Γ β).hom ▷ (M.obj A ⊗ M.obj B)) =
      ((closeEnvIso M Γ β).hom ▷ M.obj (product A B)) ≫
        (envObj M (Ctx.nil : Ctx Empty τ) (prepend (freeSlots Γ) β) ◁ (M.productIso A B).hom) :=
      MonoidalCategory.whisker_exchange _ _
    erw [← J.map_comp_assoc (envPairHom M Γ β A B), closeEnv_pair, J.map_comp_assoc,
      ← J.map_comp_assoc, exchange, J.map_comp_assoc, bind_pre_map]
  | @case _ β _ _ _ A B _ _ _ _ ih₁ ih₂ ih₃ =>
    simp only [closeDerivation, denote, ih₁, ih₂, ih₃, Category.assoc]
    erw [← J.map_comp_assoc (envSnocIso M Γ β A).hom, closeEnv_snoc, J.map_comp_assoc,
      ← J.map_comp_assoc (envSnocIso M Γ β B).hom, closeEnv_snoc, J.map_comp_assoc, case_pre_map]
  | iter _ _ ih₁ ih₂ =>
    simp only [closeDerivation, denote, ih₁, ih₂, Category.assoc]
    erw [← J.map_comp_assoc, closeEnv_snoc, J.map_comp_assoc, contextualLoop_pre_map, bind_pre_map]

public theorem denote_eq_iff_closed
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denote J M da = denote J M db ↔
      denote J M (closeDerivation da) = denote J M (closeDerivation db) := by
  rw [denote_close J M da, denote_close J M db]
  exact cancel_epi (J.map ((closeEnvIso M Γ β).hom))

public theorem typingCoherent_named_of_closing
    (closed : TypingCoherent (ν := Empty) J M Φ) :
    TypingCoherent (ν := ν) J M Φ := by
  intro Δ n β t A d e
  exact (denote_eq_iff_closed J M d e).mpr (closed (closeDerivation d) (closeDerivation e))

end Denotation

section BoundValidity
open Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.NamedContext

variable {τ₀ Φ₀ ε₀ : Type} [TypeFormers τ₀] [HasTy Φ₀ τ₀] [HasEff Φ₀ ε₀]
  [DecidableEq ν] {Γ : Ctx ν τ₀} (pe : ε₀)

private theorem namedAbortEquiv_of_closedValidity
    (visible : AllSlotsVisible Γ)
    {n : Nat} {β : BoundCtx τ₀ n} {a b : Tm ν Φ₀ n} {A : τ₀}
    (da : Derivation Φ₀ Γ β a A) (db : Derivation Φ₀ Γ β b A)
    (h : RepairedLocallySmallValidity pe (closeDerivation da) (closeDerivation db)) :
    AbortEquiv pe Γ β a b A :=
  ReopeningProofs.reopen_abortEquiv pe visible da.toHasType db.toHasType
    ((abortEquiv_iff_repairedLocallySmallValidity pe (closeDerivation da) (closeDerivation db)).mpr h)

public theorem abortEquiv_iff_repairedNamedLocallySmallValidity (visible : AllSlotsVisible Γ)
    {n : Nat} {β : BoundCtx τ₀ n} {a b : Tm ν Φ₀ n} {A : τ₀}
    (da : Derivation Φ₀ Γ β a A) (db : Derivation Φ₀ Γ β b A) :
    AbortEquiv pe Γ β a b A ↔ RepairedNamedLocallySmallValidity pe da db := by
  constructor
  · intro h V C _ _ _ _ _ _ _ _ _ _ _ _ J _ _ M _ coherent shared pureInstr
    exact denote_abortEquiv_of_coherent_shared_tensor J M coherent shared pureInstr h da db
  · intro valid
    apply namedAbortEquiv_of_closedValidity pe visible da db
    intro V C _ _ _ _ _ _ _ _ _ _ _ _ J _ _ M _ coherent shared pureInstr
    exact (denote_eq_iff_closed J M da db).mp
      (valid J M (typingCoherent_named_of_closing J M coherent) shared pureInstr)

end BoundValidity

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.NamedContext.DenotationProofs
