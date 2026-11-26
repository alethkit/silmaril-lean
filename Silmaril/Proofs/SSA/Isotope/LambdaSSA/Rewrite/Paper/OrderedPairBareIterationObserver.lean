module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Bare.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.ITree.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms

/-! # A rewrite-invariant diagnostic observation of bare feedback -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationObserver

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Bare (rawStep rawStep_typed)
open Paper.TypeCategory.ITree.Reflection
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding (AddBinding)
open CfgEta (singleCfg)

local notation "FixtureTy" => Ty Atom

/-- Retag a primitive only when it is the head of a region case scrutinee. -/
private def retagScrutinee : Tm Op → Tm Op
  | .op _ a => .op .query a
  | a => a

private def retagCases : Region Op → Region Op
  | .br ℓ a => .br ℓ a
  | .let₁ a r => .let₁ a (retagCases r)
  | .let₂ a r => .let₂ a (retagCases r)
  | .case a l r => .case (retagScrutinee a) (retagCases l) (retagCases r)
  | .cfg e n bs => .cfg (retagCases e) n (fun i => retagCases (bs i))

variable {Γ Δ : VCtx FixtureTy} {L K : LCtx FixtureTy} {r s : Region Op} {A B : FixtureTy}

private theorem retagScrutinee_typed {a : Tm Op} (ha : Tm.HasType Γ a A) : Tm.HasType Γ (retagScrutinee a) A := by
  cases ha <;> constructor <;> assumption

private theorem retagCases_typed (hr : HasType Γ r L) : HasType Γ (retagCases r) L := by
  induction hr with
  | br hℓ ha => exact .br hℓ ha
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case (retagScrutinee_typed ha) il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib

private theorem retagScrutinee_value {a : Tm Op} (ha : Tm.BranchValue Γ a A) : retagScrutinee a = a := by
  cases ha <;> rfl

private theorem retagCases_values (hr : ValueBranches Γ r L) : ValueBranches Γ (retagCases r) L := by
  induction hr with
  | br hℓ ha => exact .br hℓ ha
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case (retagScrutinee_typed ha) il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib

private theorem retagCases_renameLabels (r : Region Op) (ρ : Nat → Nat) :
    retagCases (r.renameLabels ρ) = (retagCases r).renameLabels ρ := by
  induction r generalizing ρ <;> simp_all only [retagCases, renameLabels]

private theorem retagScrutinee_rename (a : Tm Op) (ρ : Nat → Nat) :
    retagScrutinee (a.rename ρ) = (retagScrutinee a).rename ρ := by
  cases a <;> rfl

private theorem retagCases_renameVars (r : Region Op) (ρ : Nat → Nat) :
    retagCases (r.renameVars ρ) = (retagCases r).renameVars ρ := by
  induction r generalizing ρ <;> simp_all only [retagCases, renameVars, retagScrutinee_rename]

private theorem retagScrutinee_subst {a : Tm Op} (ha : Tm.HasType Γ a A) {θ : Nat → Tm Op}
    (hθ : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) :
    retagScrutinee (a.subst θ) = (retagScrutinee a).subst θ := by
  cases ha with
  | var hi => exact retagScrutinee_value (hθ hi)
  | _ => rfl

private theorem liftValues {θ : Nat → Tm Op}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) (B : FixtureTy) :
    ∀ ⦃i A⦄, At (B :: Γ) i A → Tm.BranchValue (B :: Δ) (Tm.liftSubst θ i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .var rfl
  | succ i =>
    change Tm.BranchValue (B :: Δ) ((θ i).rename Nat.succ) A
    rw [Tm.rename_eq_subst]
    exact (hθ hi).subst (fun _ _ h => .var (Ren.wk Δ B h))

private theorem retagCases_subst (hr : HasType Γ r L) {θ : Nat → Tm Op}
    (hθ : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) :
    retagCases (r.substVars θ) = (retagCases r).substVars θ := by
  induction hr generalizing Δ θ with
  | br _ ha => rfl
  | let₁ _ _ ih => simp only [retagCases, substVars, ih (liftValues hθ _)]
  | let₂ _ _ ih => simp only [retagCases, substVars, Tm.liftSubstN, ih (liftValues (liftValues hθ _) _)]
  | case ha _ _ il ir => simp only [retagCases, substVars, retagScrutinee_subst ha hθ, il (liftValues hθ _), ir (liftValues hθ _)]
  | cfg R _ _ ie ib =>
    simp only [retagCases, substVars, ie hθ, funext (fun i => ib i (liftValues hθ (R i)))]

private theorem retagCases_liftVars (σ : Nat → Region Op) :
    (fun i => retagCases (liftLSubstVars σ i)) = liftLSubstVars (fun i => retagCases (σ i)) :=
  funext fun i => retagCases_renameVars (σ i) _

private theorem retagCases_liftLabels (n : Nat) (σ : Nat → Region Op) :
    (fun i => retagCases (liftLSubstN n σ i)) = liftLSubstN n (fun i => retagCases (σ i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [liftLSubstN, liftLSubst, retagCases_renameLabels] using
        congrArg (fun f : Nat → Region Op => (f i).renameLabels Nat.succ) ih

private theorem singleValues {a : Tm Op} (ha : Tm.BranchValue Γ a A) :
    ∀ ⦃i T⦄, At (A :: Γ) i T → Tm.BranchValue Γ (Tm.singleSubst a i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ i => exact .var hi

private theorem retagCases_lsubst (hr : ValueBranches Γ r L) {σ : Nat → Region Op}
    (hσ : LSubst.HasType Γ L K σ) :
    retagCases (r.lsubst σ) = (retagCases r).lsubst (fun i => retagCases (σ i)) := by
  induction hr generalizing K σ with
  | br hℓ ha => exact retagCases_subst (hσ hℓ) (singleValues ha)
  | let₁ ha _ ih =>
    simp only [retagCases, lsubst, ih (hσ.liftVars _), retagCases_liftVars]
  | let₂ ha _ ih =>
    simp only [retagCases, lsubst, ih ((hσ.liftVars _).liftVars _), retagCases_liftVars]
  | case ha _ _ il ir =>
    simp only [retagCases, lsubst, il (hσ.liftVars _), ir (hσ.liftVars _), retagCases_liftVars]
  | cfg R _ _ ie ib =>
    have hlabels := hσ.append (List.ofFn R)
    simp only [List.length_ofFn] at hlabels
    simp only [retagCases, lsubst, ie hlabels, retagCases_liftLabels, retagCases_liftVars,
      funext (fun i => ib i (hlabels.liftVars (R i)))]

private theorem cfg_retagCases (h : CfgEquiv Γ r s L) : CfgEquiv Γ (retagCases r) (retagCases s) L := by
  induction h with
  | refl h => exact .refl (retagCases_typed h)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case (retagScrutinee_typed ha) il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | cfgZero he _ => exact .cfgZero (retagCases_typed he) _
  | cfgBrExit R hℓ ha hb =>
    simpa only [retagCases] using
      CfgEquiv.cfgBrExit R hℓ ha (fun i => retagCases_typed (hb i))
  | cfgBrLocal R i ha hb =>
    simpa only [retagCases] using
      CfgEquiv.cfgBrLocal R i ha (fun j => retagCases_typed (hb j))

private theorem native_retagCases (h : RewriteEquiv Γ r s L) : RewriteEquiv Γ (retagCases r) (retagCases s) L := by
  induction h with
  | entry h => exact .entry (cfg_retagCases h)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case (retagScrutinee_typed ha) il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | letBr ha hb hℓ =>
    simpa only [retagCases] using
      RewriteEquiv.letBr ha hb hℓ
  | caseInl ha hl hr => exact .caseInl ha (retagCases_typed hl) (retagCases_typed hr)
  | caseInr hb hl hr => exact .caseInr hb (retagCases_typed hl) (retagCases_typed hr)

private theorem replaceValues {a : Tm Op} (ha : Tm.BranchValue (B :: Γ) a A) :
    ∀ ⦃i T⦄, At (A :: Γ) i T → Tm.BranchValue (B :: Γ) (Tm.replaceNewest a i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ i => exact .var hi

private theorem substEqv_retagCases (h : SubstitutionEquiv Γ r s L) : SubstitutionEquiv Γ (retagCases r) (retagCases s) L := by
  induction h with
  | base h => exact .base (native_retagCases h)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case (retagScrutinee_typed ha) il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | letValue ha hr =>
    rw [retagCases_subst hr (singleValues ha)]
    exact .letValue ha (retagCases_typed hr)
  | @caseValue Γ a A B r L ha hr =>
    have hl : Tm.BranchValue (A :: Γ) (.inl (.var 0) : Tm Op) (coprod A B) := .inl (.var rfl)
    have hb : Tm.BranchValue (B :: Γ) (.inr (.var 0) : Tm Op) (coprod A B) := .inr (.var rfl)
    rw [retagCases_subst hr (singleValues ha)]
    simp only [retagCases, retagScrutinee_value ha, retagCases_subst hr (replaceValues hl), retagCases_subst hr (replaceValues hb)]
    exact .caseValue ha (retagCases_typed hr)
  | @caseCfg Γ e A B l L r he hl hr =>
    have arms (i : Fin 2) : retagCases (Fin.cases l (fun _ => r) i) = Fin.cases (retagCases l) (fun _ => retagCases r) i := by
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    simpa only [caseCfg, retagCases, retagScrutinee, retagCases_renameLabels, arms] using
      SubstitutionEquiv.caseCfg (retagScrutinee_typed he) (retagCases_typed hl) (retagCases_typed hr)
  | initial ha hr hs => exact .initial ha (retagCases_typed hr) (retagCases_typed hs)
  | cfgOutward R hr hb =>
    simpa only [retagCases, retagCases_renameLabels] using
      SubstitutionEquiv.cfgOutward R (retagCases_typed hr) (fun i => retagCases_typed (hb i))

private theorem singleCfg_values {e p : Region Op} (he : ValueBranches Γ e (A :: L))
    (hp : ValueBranches (A :: Γ) p (A :: L)) : ValueBranches Γ (singleCfg e p) L :=
  .cfg (fun _ : Fin 1 => A) he (fun _ => hp)

private theorem reentry_values {b : Region Op} (hb : ValueBranches (A :: Γ) b (A :: L)) :
    LSubst.ValueFamily Γ (A :: L) L (CfgEta.reentry b) := by
  intro i D hi
  exact .cfg (fun _ : Fin 1 => A) (.br hi (.var (i := 0) rfl))
    (fun _ => hb.renameVars ((Ren.wk Γ D).lift A))

private theorem cfgEta_retagCases (h : CfgEta.Eqv Γ r s L) : CfgEta.Eqv Γ (retagCases r) (retagCases s) L := by
  induction h with
  | native h => exact .native (substEqv_retagCases h)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case (retagScrutinee_typed ha) il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | @etaPost Γ A L e b K σ he hb hσ =>
    rw [retagCases_lsubst (singleCfg_values he hb) hσ,
      retagCases_lsubst (he.lsubst (reentry_values hb)) hσ]
    have hm (i : Nat) : retagCases (CfgEta.reentry (Φ := Op) b i) = CfgEta.reentry (retagCases b) i := by
      simp only [CfgEta.reentry, cfgEntryContinuations, retagCases, retagCases_renameVars]
    have hrt : LSubst.HasType _ _ _ (CfgEta.reentry b) := fun _ _ hi => (reentry_values hb hi).hasType
    rw [retagCases_lsubst he hrt]
    simp only [hm, singleCfg, retagCases]
    exact .etaPost (retagCases_values he) (retagCases_values hb) (fun _ _ hi => retagCases_typed (hσ hi))

private theorem consValues {a b : Tm Op} (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue Γ b B) :
    ∀ ⦃i T⦄, At (B :: A :: Γ) i T → Tm.BranchValue Γ (Tm.consSubst b (Tm.singleSubst a) i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact hb
  | succ i => exact singleValues ha hi

private theorem uniform_retagCases {A D : FixtureTy} {entry p q : Region Op} {a : Tm Op}
    (he : ValueBranches Γ entry (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : HasType (D :: Γ) q (D :: L)) (ha : Tm.BranchValue (A :: Γ) a D)
    (square : Paper.Eqv (A :: Γ)
      (retagCases (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a))))
      (retagCases ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => q)))) (D :: L)) :
    Paper.Eqv Γ (retagCases (singleCfg entry p))
      (retagCases (singleCfg (entry.lsubst (CfgEta.Uniformity.localMap a)) q)) L := by
  have hm : LSubst.HasType Γ (A :: L) (D :: L) (CfgEta.Uniformity.localMap a) :=
    CfgEta.Uniformity.localMap_typed ha.hasType
  have sameMap : (fun i => retagCases (CfgEta.Uniformity.localMap a i)) = CfgEta.Uniformity.localMap a := by
    funext i
    cases i with
    | zero => rfl
    | succ i => rfl
  have hbr : ValueBranches (A :: Γ) (.br 0 a) [D] := .br (ℓ := 0) rfl ha
  have hqFamily : LSubst.HasType Γ [D] (D :: L) (fun _ => q) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hq
  rw [retagCases_lsubst hp (hm.liftVars A), retagCases_liftVars, sameMap,
    retagCases_lsubst hbr (hqFamily.liftVars A), retagCases_liftVars] at square
  simpa only [singleCfg, retagCases, retagCases_lsubst he hm, sameMap] using
    Paper.Eqv.uniform (retagCases_values he) (retagCases_values hp) (retagCases_typed hq) ha square

private theorem paper_retagCases (h : Paper.Eqv Γ r s L) : Paper.Eqv Γ (retagCases r) (retagCases s) L := by
  induction h with
  | cfgEta h => exact .cfgEta (cfgEta_retagCases h)
  | productBeta h =>
    cases h with
    | let₂Beta ha hb hr =>
      rw [retagCases_subst hr (consValues ha hb)]
      exact .productBeta (.let₂Beta ha hb (retagCases_typed hr))
  | productEta h =>
    cases h with
    | let₂Eta hi hℓ => exact .productEta (.let₂Eta hi hℓ)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case (retagScrutinee_typed ha) il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | lsubstCongr hp h ih =>
    rw [retagCases_lsubst hp (fun _ _ hi => (h hi).typed.1), retagCases_lsubst hp (fun _ _ hi => (h hi).typed.2)]
    exact .lsubstCongr (retagCases_values hp) ih
  | lsubstPost h hr hs hσ ih =>
    rw [retagCases_lsubst hr hσ, retagCases_lsubst hs hσ]
    exact .lsubstPost ih (retagCases_values hr) (retagCases_values hs) (fun _ _ hi => retagCases_typed (hσ hi))
  | substVars h hθ ih =>
    rw [retagCases_subst h.typed.1 hθ, retagCases_subst h.typed.2 hθ]
    exact .substVars ih hθ
  | renameLabels h hρ ih =>
    simp only [retagCases_renameLabels]
    exact .renameLabels ih hρ
  | @collapsePost Γ e A L p K σ he hp hσ =>
    have hl : ValueBranches Γ (CfgEta.Codiagonal.nested e p) L :=
      singleCfg_values he (singleCfg_values (.br (ℓ := 0) rfl (.var (i := 0) rfl))
        (hp.renameVars ((Ren.wk Γ A).lift A)))
    have hr : ValueBranches Γ (CfgEta.Codiagonal.flattened e p) L := by
      apply singleCfg_values he
      rw [renameLabels_eq_lsubst]
      exact hp.lsubst (fun i _ hi => .br (ℓ := i.pred) (CfgEta.Codiagonal.mergeLabels A L hi) (.var rfl))
    rw [retagCases_lsubst hl hσ, retagCases_lsubst hr hσ]
    simpa only [CfgEta.Codiagonal.nested, CfgEta.Codiagonal.flattened, singleCfg, retagCases,
      retagCases_renameVars, retagCases_renameLabels] using
        Paper.Eqv.collapsePost (retagCases_values he) (retagCases_values hp) (fun _ _ hi => retagCases_typed (hσ hi))
  | uniform he hp hq ha _ ih => exact uniform_retagCases he hp hq ha ih

variable {Seed : VCtx FixtureTy → Region Op → Region Op → LCtx FixtureTy → Prop}

private theorem extension_retagCases (fixed : ∀ {Γ r s L}, Seed Γ r s L → retagCases r = r ∧ retagCases s = s)
    (h : Paper.Extension.Eqv Seed Γ r s L) : Paper.Extension.Eqv Seed Γ (retagCases r) (retagCases s) L := by
  induction h with
  | paper h => exact .paper (paper_retagCases h)
  | extra hr hs h =>
    obtain ⟨hl, hr'⟩ := fixed h
    rw [hl, hr']
    exact .extra hr hs h
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case (retagScrutinee_typed ha) il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | lsubstCongr hp h ih =>
    rw [retagCases_lsubst hp (fun _ _ hi => (h hi).typed.1), retagCases_lsubst hp (fun _ _ hi => (h hi).typed.2)]
    exact .lsubstCongr (retagCases_values hp) ih
  | lsubstPost h hr hs hσ ih =>
    rw [retagCases_lsubst hr hσ, retagCases_lsubst hs hσ]
    exact .lsubstPost ih (retagCases_values hr) (retagCases_values hs) (fun _ _ hi => retagCases_typed (hσ hi))
  | substVars h hθ ih =>
    rw [retagCases_subst h.typed.1 hθ, retagCases_subst h.typed.2 hθ]
    exact .substVars ih hθ
  | renameLabels h hρ ih =>
    simp only [retagCases_renameLabels]
    exact .renameLabels ih hρ


open CategoryTheory
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding (pairJoined_guarded_eqv_iff)
open SyntacticCategory (iterationBody iterationDispatch iterateRegion)
open Silmaril.Elgot.ITree
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

attribute [local instance] typeModel categoricalInstructions

local notation "Join" => Paper.WithPairReturns.JoinedStep (τ := Ty Atom) (Φ := Op) false
local notation "Added" => _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Bare.Seed
local notation "J" => typeJ (m := TreeModel)
local notation "M" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)

open CfgEta.TypeCategory (returnRegion returnRegion_typed)

private theorem retagCases_return {a : Tm Op} (ha : Tm.HasType Γ a A) : retagCases (returnRegion a) = returnRegion a := by
  induction ha with
  | @let₁ Γ a b B A ha hb iha ihb =>
    have ht : LSubst.HasType Γ [B] [A] (fun _ => returnRegion b) :=
      fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸
        (returnRegion_typed hb).hasType
    rw [returnRegion, retagCases_lsubst (returnRegion_typed ha) ht, iha]
    simp only [ihb]
  | _ => rfl

private theorem added_fixed (h : Added Γ r s L) : retagCases r = r ∧ retagCases s = s := by
  rcases h with (((h | (h | h)) | h) | h)
  · cases h with
    | inl h => cases h <;> exact ⟨rfl, rfl⟩
    | inr h => cases h; exact ⟨rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl⟩
  · cases h with
    | split ha hb _ _ =>
      refine ⟨rfl, ?_⟩
      simp only [retagCases, retagScrutinee, retagCases_renameVars, retagCases_return ha, retagCases_return hb]
  · cases h; exact ⟨rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl⟩

private abbrev x : Ty.denote Atoms payload := ⟨0⟩
private abbrev env : Env (Sigma Atoms) := extend (fun _ => .unit) (encodeValue Atoms payload x)

set_option backward.isDefEq.respectTransparency false in
private theorem observes {r s : Region Op} (hr : ValueBranches [payload] r [payload])
    (hs : ValueBranches [payload] s [payload]) (h : Paper.Extension.Eqv Added [payload] r s [payload]) :
    region raw env r = region raw env s := by
  let := regionTypingCoherent raw compatible
  have hg := (pairJoined_guarded_eqv_iff hr hs).mp h
  have he := congrArg (fun f : Paper.Extension.Singleton.ofType Join payload ⟶ Paper.Extension.Singleton.ofType Join payload =>
      (Paper.WithPairReturns.ITree.interpretation.map f).of x)
    ((ofRegion_eq_iff Join hr hs).mpr hg)
  change ((Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)
      (Paper.WithPairReturns.joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false)).map
        (ofRegion Join hr)).of x =
    ((Paper.Extension.Singleton.denoteFunctor J M (fun _ _ => ⟨rfl, rfl⟩)
      (Paper.WithPairReturns.joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false)).map
        (ofRegion Join hs)).of x at he
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion,
    Paper.Extension.Singleton.denoteFunctor_map_ofRegion] at he
  exact (singletonDenote_tree raw compatible hr.hasType x (fun _ => .unit)).symm.trans
    ((congrArg (fun z : TreeModel (Ty.denote Atoms payload) =>
      z >>= fun b => pure (0, encodeValue Atoms payload b)) he).trans
      (singletonDenote_tree raw compatible hs.hasType x (fun _ => .unit)))

private theorem distinct {Y : Type 1} (k l : Sum Nat Nat → ModelTree Call Y) :
    vis (Call.request .query 0) k ≠ vis (Call.request .poll 0) l := by
  intro h
  have seen := congrArg out h
  simp only [out_vis, Part.some_inj, Visible.vis.injEq, heq_eq_eq, true_and, and_true,
    Call.request.injEq] at seen
  cases seen.1

private abbrev poll : Tm Op := .op .poll (.var 0)

private theorem mergeLabels : Ren [payload, payload] [payload] (fun _ => 0) := by
  intro i A hi
  have he := List.mem_of_getElem? hi
  have he : A = payload := by simpa using he
  exact he.symm ▸ rfl

/-- Even after adjoining the branch-binding rule, the literal case/let comparison fails. -/
theorem case_bind_separation :
    ¬ Paper.Extension.Eqv Added [payload] (iterationBody rawStep)
      (iterationBody rawStep.bindBranchArguments) [payload, payload] := by
  intro h
  have hm := Paper.Extension.Eqv.renameLabels (extension_retagCases added_fixed h) mergeLabels
  let l : Region Op := .case (.op .query (.var 0)) (.br 0 (.var 0)) (.br 0 (.var 0))
  let r : Region Op := .let₁ poll (.case (.var 0) (.br 0 (.var 0)) (.br 0 (.var 0)))
  change Paper.Extension.Eqv Added [payload] l r [payload] at hm
  have hl : ValueBranches [payload] l [payload] :=
    .case (.op (.var rfl)) (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 0) rfl (.var rfl))
  have hr : ValueBranches [payload] r [payload] := .let₁ (.op (.var rfl))
    (.case (.var rfl) (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 0) rfl (.var rfl)))
  have he := observes hl hr hm
  simp only [l, r, region, term, raw, env, encodeValue, extend, pure_bind, vis_bind] at he
  exact distinct _ _ he


/-- The separating equation has guarded endpoints even before closing the loop. -/
theorem case_bind_endpoints_guarded :
    ValueBranches [payload] (iterationBody rawStep) [payload, payload] ∧
      ValueBranches [payload] (iterationBody rawStep.bindBranchArguments) [payload, payload] :=
  ⟨.case (.op (.var rfl)) (.br (ℓ := 1) rfl (.var rfl)) (.br (ℓ := 0) rfl (.var rfl)),
    .let₁ (.op (.var rfl)) (SyntacticCategory.iterationDispatch_valueBranches payload payload)⟩

private abbrev loop (p : Region Op) : Region Op :=
  feedbackRegion [payload] (fun _ => p) 0

private abbrev queryBody : Region Op :=
  .case (.op .query (.var 0)) (.br 1 (.var 0)) (.br 0 (.var 0))

private abbrev pollBody : Region Op := .let₁ poll iterationDispatch

private theorem loop_typed {p : Region Op} (hp : ValueBranches [payload] p [payload, payload]) :
    ValueBranches [payload] (loop p) [payload] :=
  .cfg (fun _ : Fin 1 => payload) (.br (ℓ := 0) rfl (.var rfl))
    (fun _ => hp.renameVars ((Ren.wk [] payload).lift payload))

private abbrev initial : Silmaril.Isotope.Value (Sigma Atoms) := encodeValue Atoms payload x

private theorem loop_first (p : Region Op) (op : Op) (k : Sum Nat Nat → TreeModel (Transfer (Sigma Atoms)))
    (h : region raw (extend env initial) (p.renameVars (DeBruijn.lift Nat.succ)) =
      vis (.request op 0) k) :
    ∃ k' : Sum Nat Nat → TreeModel (Transfer (Sigma Atoms)),
      region raw env (loop p) = vis (.request op 0) k' := by
  let step : BlockInput (Sigma Atoms) 1 → TreeModel (Transfer (Sigma Atoms) ⊕ BlockInput (Sigma Atoms) 1) :=
    fun q => region raw (extend env q.2) (p.renameVars (DeBruijn.lift Nat.succ)) >>= fun out =>
      pure (splitTransfer 1 out)
  have he : region raw env (loop p) = Silmaril.Elgot.iter step (0, initial) := by
    simp only [loop, feedbackRegion, cfgEntryContinuations, region, term, pure_bind]
    rfl
  rw [he]
  rw [congrFun (iterate_fixpoint step) (0, initial)]
  change ∃ k', ((region raw (extend env initial) (p.renameVars (DeBruijn.lift Nat.succ)) >>=
    fun out => pure (splitTransfer 1 out)) >>= Sum.elim pure (Silmaril.Elgot.iter step)) = _
  rw [h, vis_bind, vis_bind]
  exact ⟨_, rfl⟩

private def dispatchReply (a : Sum Nat Nat) : TreeModel (Transfer (Sigma Atoms)) :=
  match encodeValue Atoms Output (reply a) with
  | .inl v => pure (1, v)
  | .inr v => pure (0, v)
  | _ => diverge

/-- The bare and bind-first CFGs already differ at the same exactly typed raw step. -/
theorem bare_iterate_separation :
    ¬ Paper.Extension.Eqv Added [payload] (iterateRegion payload rawStep)
      (iterateRegion payload rawStep.bindBranchArguments) [payload] := by
  intro h
  have hm := extension_retagCases added_fixed h
  change Paper.Extension.Eqv Added [payload] (loop queryBody) (loop pollBody) [payload] at hm
  have hq : ValueBranches [payload] queryBody [payload, payload] :=
    .case (.op (.var rfl)) (.br (ℓ := 1) rfl (.var rfl)) (.br (ℓ := 0) rfl (.var rfl))
  have hp : ValueBranches [payload] pollBody [payload, payload] :=
    .let₁ (.op (.var rfl)) (SyntacticCategory.iterationDispatch_valueBranches payload payload)
  have htree := observes (loop_typed hq) (loop_typed hp) hm
  obtain ⟨k, hk⟩ := loop_first queryBody .query dispatchReply (by
    simp only [renameVars, Tm.rename, DeBruijn.lift, region, term, raw,
      initial, encodeValue, extend, pure_bind, vis_bind]
    apply (vis_inj _ _ _).mpr
    funext reply
    cases reply <;> rfl)
  obtain ⟨l, hl⟩ := loop_first pollBody .poll dispatchReply (by
    simp only [iterationDispatch, renameVars, Tm.rename, DeBruijn.lift, region, term, raw,
      initial, encodeValue, extend, pure_bind, vis_bind]
    apply (vis_inj _ _ _).mpr
    funext reply
    cases reply <;> rfl)
  exact distinct k l (hk.symm.trans (htree.trans hl))

/-- The bare literal operation does not respect the raw branch-binding quotient. -/
theorem bare_iterate_not_congruent :
    ¬ (∀ {r s : Region Op}, Paper.Extension.Eqv Added [payload] r s [Output] →
      Paper.Extension.Eqv Added [payload] (iterateRegion payload r) (iterateRegion payload s) [payload]) := by
  intro h
  have he := Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.bindBranchArguments_eqv_addBinding
    (Seed := Join) rawStep_typed
  exact bare_iterate_separation (h he)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationObserver
