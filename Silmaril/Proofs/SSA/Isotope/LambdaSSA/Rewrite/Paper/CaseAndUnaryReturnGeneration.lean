module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Soundness.Thms

/-! # Generating returning terms in the case-return and unary-forwarding quotient -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseAndUnaryReturnGeneration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseAndUnaryReturns
open CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (returnRegion_typed seqValueBranches caseValueBranches)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff)
open Paper.Extension.Singleton.Generation (Generated generated_branchValue generated_primitive_branchValue)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.RetainedLet (returnOnce_typed unpackBody_typed diagonal_typed)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

section Returns

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (contains : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Step pe Γ r s L → Seed Γ r s L)

set_option hygiene false in
local notation "Lit" => ofRegion Seed

set_option hygiene false in
local notation "P" => Paper.Extension.Singleton.projection Seed

variable {X A B D : τ} {a b : Tm Φ}

set_option backward.isDefEq.respectTransparency false in
include contains in
theorem returnCase_eq_copair (ha : Tm.HasType [A] a D) (hb : Tm.HasType [B] b D)
    (pa : Tm.Pure pe a) (pb : Tm.Pure pe b) :
    Lit (returnRegion_typed (.case (.var (i := 0) rfl)
      (ha.rename ((Ren.wk [] (coprod A B)).lift A)) (hb.rename ((Ren.wk [] (coprod A B)).lift B)))) =
      exactCopair (Seed) (Lit (returnRegion_typed ha)) (Lit (returnRegion_typed hb)) := by
  rw [Paper.Extension.Singleton.Generation.exactCopair_ofRegion]
  apply (ofRegion_eq_iff (Seed) _ _).2
  exact .extra (returnRegion_typed (.case (.var (i := 0) rfl)
    (ha.rename ((Ren.wk [] (coprod A B)).lift A)) (hb.rename ((Ren.wk [] (coprod A B)).lift B)))).hasType
    (caseValueBranches (returnRegion_typed ha) (returnRegion_typed hb)).hasType
    (contains (includeCase pe (.split ha hb pa pb)))

set_option backward.isDefEq.respectTransparency false in
include contains in
theorem returnLet_eq_let (ha : Tm.HasType [X] a A) (hb : Tm.HasType [A, X] b D) :
    Lit (returnRegion_typed (.let₁ ha hb)) = Lit (.let₁ ha (returnRegion_typed hb)) := by
  apply (ofRegion_eq_iff (Seed) _ _).2
  refine (Paper.UnaryReturn.returnRegion_eq_returnOnce (fun h => contains (includeUnary pe h)) (.let₁ ha hb)).trans ?_
  have step := Paper.UnaryReturn.Step.fuse ha hb
  exact (Paper.Extension.Eqv.extra step.typed.1 step.typed.2 (contains (includeUnary pe step))).symm.trans
    (.let₁ ha (Paper.UnaryReturn.returnRegion_eq_returnOnce (fun h => contains (includeUnary pe h)) hb).symm)

set_option backward.isDefEq.respectTransparency false in
include contains in
theorem generated_returnLet {r : Region Φ} (ha : Tm.HasType [X] a A)
    (hr : ValueBranches [A, X] r [D]) (g₁ : Generated (Seed) (Lit (returnRegion_typed ha)))
    (g₂ : Generated (Seed) (Lit (unpackBody_typed hr))) :
    Generated (Seed) (Lit (.let₁ ha hr)) := by
  have h : Lit (returnRegion_typed ha) = Lit (returnOnce_typed ha) :=
    (ofRegion_eq_iff (Seed) _ _).2 (Paper.UnaryReturn.returnRegion_eq_returnOnce (fun h => contains (includeUnary pe h)) ha)
  have gr := h ▸ g₁
  let diag := diagonal_typed (Φ := Φ) X
  let scrutinee := returnOnce_typed ha
  let retained := CfgEta.TypeCategory.whiskerLeftRegion_typed X scrutinee
  let pack := unpackBody_typed hr
  let sequenced := seqValueBranches diag retained
  let body := seqValueBranches sequenced pack
  have eq : Lit body = Lit (.let₁ ha hr) :=
    (ofRegion_eq_iff (Seed) body (.let₁ ha hr)).2 (.paper (Paper.RetainedLet.literal_let ha hr.hasType))
  rw [← eq]
  change Generated (Seed) ((P).map (Paper.TypeCategory.ofRegion body))
  rw [← Paper.TypeCategory.ofRegion_comp sequenced pack body,
    ← Paper.TypeCategory.ofRegion_comp diag retained sequenced,
    ← Paper.TypeCategory.whiskerLeft_ofRegion X scrutinee, (P).map_comp, (P).map_comp]
  exact .comp (.comp (.copy X) (.left X gr)) g₂

include contains in
/-- A returning let with a genuinely retained input uses the returned
scrutinee and the body at its packed product input. -/
theorem generated_retained_returnLet (ha : Tm.HasType [X] a A) (hb : Tm.HasType [A, X] b D)
    (g₁ : Generated (Seed) (Lit (returnRegion_typed ha)))
    (g₂ : Generated (Seed) (Lit (unpackBody_typed (returnRegion_typed hb)))) :
    Generated (Seed) (Lit (returnRegion_typed (.let₁ ha hb))) :=
  (returnLet_eq_let pe Seed contains ha hb).symm ▸ generated_returnLet pe Seed contains ha (returnRegion_typed hb) g₁ g₂

set_option backward.isDefEq.respectTransparency false in
theorem returnLet_eq_comp (ha : Tm.HasType [X] a A) (hb : Tm.HasType [A] b D) :
    Lit (returnRegion_typed (.let₁ ha (hb.rename ((Ren.wk [] X).lift A)))) =
      Lit (returnRegion_typed ha) ≫ Lit (returnRegion_typed hb) :=
  ((P).map_comp _ _).symm.trans (congrArg (P).map (Paper.TypeCategory.returnTerm_comp ha hb)) |>.symm

set_option backward.isDefEq.respectTransparency false in
include contains in
theorem generated_returnFragment {t : Tm Φ} {ht : Tm.HasType [X] t D}
    (h : ReturnFragment pe ht) : Generated (Seed) (Lit (returnRegion_typed ht)) := by
  induction h with
  | value ha =>
    have eq := (ofRegion_eq_iff (Seed) (returnRegion_typed ha.hasType) (.br (ℓ := 0) rfl ha)).2
      (.paper (.cfgEta (.native (.base (CfgEta.TypeCategory.returnRegion_branchValue ha)))))
    exact eq.symm ▸ generated_branchValue (Seed) ha
  | primitive p ht => exact generated_primitive_branchValue (Seed) p ht
  | @seq X A D a b ha hb _ _ ga gb =>
    rw [returnLet_eq_comp Seed ha hb]
    exact .comp ga gb
  | @caseInput A B D a b ha hb pa pb _ _ ga gb =>
    rw [returnCase_eq_copair pe Seed contains ha hb pa pb]
    exact .copair ga gb

end Returns

set_option hygiene false in
local notation "Seed" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Joined" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Lit" => ofRegion (Seed)

section Soundness

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem eqv_sound
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (e : Paper.Extension.Eqv (Seed) Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Paper.Extension.Eqv.sound J M shared (fun step hp hq => step.elim
    (fun unary => unary.denotes J M hp hq)
    (fun cases =>
      ⟨_, denoteRegion_spec J M hp,
        (Paper.WithCaseReturns.Eqv.sound pe J M shared (.extra hp hq (Or.inr cases)) hp hq).symm ▸
          denoteRegion_spec J M hq⟩)) e hr hs


theorem joined_eqv_sound
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (e : Paper.Extension.Eqv (Joined) Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Paper.Extension.Eqv.sound J M shared (fun step hp hq => step.elim
    (fun base => Paper.WithProjectionReturnsAndUnitEta.step_denotes J M base hp hq)
    (fun returned =>
      ⟨_, denoteRegion_spec J M hp,
        (eqv_sound pe J M shared (.extra hp hq returned) hp hq).symm ▸ denoteRegion_spec J M hq⟩)) e hr hs

/-- Equality of guarded representatives implies equality of their typed
singleton interpretations in the same model. -/
theorem denoteSingleton_eq_ofRegion_eq
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {A B : τ} {r s : Region Φ} (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B])
    (e : Lit hr = Lit hs) :
    denoteSingletonRegion J M hr.hasType = denoteSingletonRegion J M hs.hasType := by
  rw [denoteSingletonRegion, denoteSingletonRegion,
    eqv_sound pe J M shared ((ofRegion_eq_iff (Seed) hr hs).1 e) hr.hasType hs.hasType]

end Soundness

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseAndUnaryReturnGeneration
