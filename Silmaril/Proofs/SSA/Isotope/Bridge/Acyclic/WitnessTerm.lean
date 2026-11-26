module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LetIter.ProofRelevant.Semantics.Categorical (bind pair caseWithContext)
open LambdaSSA.Semantics.Categorical
open scoped MonoidalCategory

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V] {J : V ⥤ C}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  (M : TypeModel υ V) (I : InstructionModel J M Q.Instr)

private theorem lookup_heq {Γ : LambdaSSA.VCtx τ} {i : Nat} {A : τ} (h : LambdaSSA.At Γ i A) :
    HEq (lookup (pullbackTypes g M) i h) (lookup M i (mapContextLookup g.ty h)) := by
  induction Γ generalizing i with
  | nil => simp [LambdaSSA.At] at h
  | cons B Γ ih =>
    cases i with
    | zero =>
      have same : B = A := by simpa [LambdaSSA.At] using h
      subst A
      rw [lookup, lookup]
      change HEq (CartesianMonoidalCategory.snd (ctxObj (pullbackTypes g M) Γ) (M.obj (g.ty B)))
        (CartesianMonoidalCategory.snd (ctxObj M (Γ.map g.ty)) (M.obj (g.ty B)))
      have hΓ := ctxObj_pullback g M Γ
      congr! (config := .unfoldSameFun)
    | succ i =>
      rw [lookup, lookup]
      have hi := ih (i := i) (show LambdaSSA.At Γ i A from h)
      have hΓ := ctxObj_pullback g M Γ
      have hc := ctxObj_pullback g M (B :: Γ)
      congr! (config := .unfoldSameFun)

omit [CartesianMonoidalCategory V] [HasFiniteCoproducts V] in
private theorem isoTrans_hom_heq {A B D : V} (e : A = B) (i : B ≅ D) :
    HEq (eqToIso e ≪≫ i).hom i.hom := by subst B; simp

omit [CartesianMonoidalCategory V] [HasFiniteCoproducts V] in
private theorem isoTrans_inv_heq {A B D : V} (e : A = B) (i : B ≅ D) :
    HEq (eqToIso e ≪≫ i).inv i.inv := by subst B; simp

omit [CartesianMonoidalCategory V] [HasFiniteCoproducts V] in
private theorem initial_to_heq {A B D : V} (e : A = B) (i : IsInitial B) :
    HEq ((cast (congrArg IsInitial e.symm) i).to D) (i.to D) := by subst B; rfl

private theorem primitive_heq (f : P.Instr) :
    HEq ((pullbackInstructions g I).denote f) (I.denote (g.instr f)) :=
  cast_heq _ _

theorem product_hom_heq (A B : τ) :
    HEq ((pullbackTypes g M).productIso A B).hom (M.productIso (g.ty A) (g.ty B)).hom :=
  isoTrans_hom_heq _ _

private theorem product_inv_heq (A B : τ) :
    HEq ((pullbackTypes g M).productIso A B).inv (M.productIso (g.ty A) (g.ty B)).inv :=
  isoTrans_inv_heq _ _

theorem coprod_hom_heq (A B : τ) :
    HEq ((pullbackTypes g M).coprodIso A B).hom (M.coprodIso (g.ty A) (g.ty B)).hom :=
  isoTrans_hom_heq _ _

private theorem coprod_inv_heq (A B : τ) :
    HEq ((pullbackTypes g M).coprodIso A B).inv (M.coprodIso (g.ty A) (g.ty B)).inv :=
  isoTrans_inv_heq _ _

private theorem unit_inv_heq :
    HEq (pullbackTypes g M).unitIso.inv M.unitIso.inv :=
  isoTrans_inv_heq _ _

private theorem empty_to_heq (A : τ) :
    HEq ((pullbackTypes g M).emptyIsInitial.to ((pullbackTypes g M).obj A))
      (M.emptyIsInitial.to (M.obj (g.ty A))) :=
  initial_to_heq (congrArg M.obj (SignatureMap.PreservesSums.empty (g := g))) M.emptyIsInitial

theorem model_product_obj_eq (A B : τ) :
    (pullbackTypes g M).obj (product A B) = M.obj (product (g.ty A) (g.ty B)) :=
  congrArg M.obj (SignatureMap.PreservesProducts.product A B)

theorem model_coprod_obj_eq (A B : τ) :
    (pullbackTypes g M).obj (coprod A B) = M.obj (coprod (g.ty A) (g.ty B)) :=
  congrArg M.obj (SignatureMap.PreservesSums.coprod A B)

theorem ctxPairIso_heq (Γ : LambdaSSA.VCtx τ) (A B : τ) :
    HEq (ctxPairIso (pullbackTypes g M) Γ A B)
      (ctxPairIso M (Γ.map g.ty) (g.ty A) (g.ty B)) := by
  unfold ctxPairIso
  have hΓ := ctxObj_pullback g M Γ
  congr! (config := .unfoldSameFun)

variable [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [DistributiveFreydCategory J]

@[expose] def TermImage (Γ : LambdaSSA.VCtx τ) (t : LambdaSSA.Tm P.Instr) (A : υ)
    {X : Type} (f : X) : Prop :=
  ∃ (ht : LambdaSSA.Tm.HasType (Γ.map g.ty) (t.mapInstr g.instr) A)
    (a : J.obj (ctxObj M (Γ.map g.ty)) ⟶ J.obj (M.obj A)),
    (letI := I; Denotes J M ht a) ∧ HEq f a

omit [TypeFormers τ] [g.PreservesProducts] [g.PreservesSums] in
theorem retargetTermWitness {Γ : LambdaSSA.VCtx τ} {t : LambdaSSA.Tm P.Instr} {A B : υ}
    {X : Type} {f : X} (e : A = B) (h : TermImage g M I Γ t A f) :
    TermImage g M I Γ t B f := e ▸ h

theorem mapTermWitness_proof {Γ : LambdaSSA.VCtx τ} {t : LambdaSSA.Tm P.Instr} {A : τ}
    {ht : LambdaSSA.Tm.HasType Γ t A}
    {f : J.obj (ctxObj (pullbackTypes g M) Γ) ⟶ J.obj ((pullbackTypes g M).obj A)}
    (d : letI := pullbackInstructions g I; Denotes J (pullbackTypes g M) ht f) :
    TermImage g M I Γ t (g.ty A) f := by
  let _ := I
  induction d with
  | @var Γ i A h =>
    refine ⟨_, _, Denotes.var (mapContextLookup g.ty h), ?_⟩
    have hl := lookup_heq g M h
    have hΓ := ctxObj_pullback g M Γ
    congr! (config := .unfoldSameFun)
  | @op Γ t f ha a da ih =>
    obtain ⟨_, a', da', ea⟩ := retargetTermWitness g M I (g.source f).symm ih
    apply retargetTermWitness g M I (g.target f)
    refine ⟨_, _, Denotes.op da', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hs := congrArg M.obj (g.source f).symm
    have ht := congrArg M.obj (g.target f).symm
    have hp := primitive_heq g M I f
    congr! (config := .unfoldSameFun)
  | @let₁ Γ a A ha fa b B hb fb da db iha ihb =>
    obtain ⟨_, fa', da', ea⟩ := iha
    obtain ⟨_, fb', db', eb⟩ := ihb
    refine ⟨_, _, Denotes.let₁ da' db', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hΓA := ctxObj_pullback g M (A :: Γ)
    congr! (config := .unfoldSameFun)
  | @pair Γ a A ha fa b B hb fb da db iha ihb =>
    obtain ⟨_, fa', da', ea⟩ := iha
    obtain ⟨_, fb', db', eb⟩ := ihb
    apply retargetTermWitness g M I (SignatureMap.PreservesProducts.product (g := g) A B).symm
    refine ⟨_, _, Denotes.pair da' db', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hprod := model_product_obj_eq g M A B
    have hp := product_inv_heq g M A B
    congr! (config := .unfoldSameFun)
  | @unit Γ =>
    apply retargetTermWitness g M I (SignatureMap.PreservesProducts.unit (g := g)).symm
    refine ⟨_, _, Denotes.unit, ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hu := unit_inv_heq g M
    have ht := congrArg M.obj (SignatureMap.PreservesProducts.unit (g := g))
    congr! (config := .unfoldSameFun)
  | @let₂ Γ a A B ha fa b D hb fb da db iha ihb =>
    obtain ⟨_, fa', da', ea⟩ := retargetTermWitness g M I
      (SignatureMap.PreservesProducts.product (g := g) A B) iha
    obtain ⟨_, fb', db', eb⟩ := ihb
    refine ⟨_, _, Denotes.let₂ da' db', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hΓAB := ctxObj_pullback g M (B :: A :: Γ)
    have hi := ctxPairIso_heq g M Γ A B
    have hp := product_hom_heq g M A B
    have ho := model_product_obj_eq g M A B
    congr! (config := .unfoldSameFun)
  | @inl Γ a A ha fa B da ih =>
    obtain ⟨_, fa', da', ea⟩ := ih
    apply retargetTermWitness g M I (SignatureMap.PreservesSums.coprod (g := g) A B).symm
    refine ⟨_, _, Denotes.inl da', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have ho := model_coprod_obj_eq g M A B
    have hi := coprod_inv_heq g M A B
    congr! (config := .unfoldSameFun)
  | @inr Γ b B hb fb A db ih =>
    obtain ⟨_, fb', db', eb⟩ := ih
    apply retargetTermWitness g M I (SignatureMap.PreservesSums.coprod (g := g) A B).symm
    refine ⟨_, _, Denotes.inr db', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have ho := model_coprod_obj_eq g M A B
    have hi := coprod_inv_heq g M A B
    congr! (config := .unfoldSameFun)
  | @case Γ e A B he fe l D hl fl r hr fr de dl dr ihe ihl ihr =>
    obtain ⟨_, fe', de', ee⟩ := retargetTermWitness g M I
      (SignatureMap.PreservesSums.coprod (g := g) A B) ihe
    obtain ⟨_, fl', dl', el⟩ := ihl
    obtain ⟨_, fr', dr', er⟩ := ihr
    refine ⟨_, _, Denotes.case de' dl' dr', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hΓA := ctxObj_pullback g M (A :: Γ)
    have hΓB := ctxObj_pullback g M (B :: Γ)
    have hc := coprod_hom_heq g M A B
    have ho := model_coprod_obj_eq g M A B
    congr! (config := .unfoldSameFun)
  | @abort Γ a ha fa A da ih =>
    obtain ⟨_, fa', da', ea⟩ := retargetTermWitness g M I (SignatureMap.PreservesSums.empty (g := g)) ih
    refine ⟨_, _, Denotes.abort da', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have he := congrArg M.obj (SignatureMap.PreservesSums.empty (g := g))
    have hd := empty_to_heq g M A
    congr! (config := .unfoldSameFun)

end Silmaril.Isotope.Institution.Acyclic
