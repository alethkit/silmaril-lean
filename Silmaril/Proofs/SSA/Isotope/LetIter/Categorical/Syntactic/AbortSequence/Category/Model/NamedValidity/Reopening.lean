module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.NamedValidity.Closing.Defs
import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms

open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasType AbortEquiv)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w r u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.NamedContext.ReopeningProofs

open NamedContext

variable {ν : Type w} {τ : Type u} {Φ : Type v}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

section Reopening

open Silmaril.Isotope.LetIter.LocallyNameless (PureTypedSubst)
variable [DecidableEq ν] {Γ : Ctx ν τ}

public theorem visible_nil : AllSlotsVisible (Ctx.nil : Ctx ν τ) := fun i => i.elim0

public theorem visible_snoc {x : ν} {A : τ} (visible : AllSlotsVisible Γ) (fresh : Γ.lookup x = none) :
    AllSlotsVisible (.snoc Γ (some x) A) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨x, by simp [lookupSlot]⟩
  · obtain ⟨y, hy⟩ := visible j
    have ne : y ≠ x := by
      intro e
      subst y
      have eq := lookupSlot_eq_lookup x Γ
      rw [hy, fresh] at eq
      cases eq
    exact ⟨y, by simp only [lookupSlot, ite_eq_right ne, hy, Option.map_some]⟩

private theorem nameIndexedSlots_lookup_none (types : List τ) {x : Nat} (hx : types.length ≤ x) :
    (nameIndexedSlots types).lookup x = none := by
  induction types with
  | nil => rfl
  | cons A rest ih =>
    have hlt : rest.length < x := Nat.lt_of_succ_le hx
    simp only [nameIndexedSlots, Ctx.lookup, ite_eq_right (Nat.ne_of_gt hlt)]
    exact ih (Nat.le_of_lt hlt)

public theorem nameIndexedSlots_visible (types : List τ) : AllSlotsVisible (nameIndexedSlots types) := by
  induction types with
  | nil => exact visible_nil
  | cons A rest ih => exact visible_snoc ih (nameIndexedSlots_lookup_none rest (Nat.le_refl _))

def slotName (Γ : Ctx ν τ) : Fin Γ.length → Option ν :=
  match Γ with
  | .nil => fun i => i.elim0
  | .snoc Γ name _ => Fin.cases name (slotName Γ)

theorem slotName_of_lookupSlot {x : ν} {i : Fin Γ.length} (h : lookupSlot x Γ = some i) :
    slotName Γ i = some x := by
  induction Γ with
  | nil => exact i.elim0
  | snoc Γ name A ih =>
    have tail (h : (lookupSlot x Γ).map Fin.succ = some i) :
        slotName (.snoc Γ name A) i = some x := by
      cases hs : lookupSlot x Γ with
      | none =>
        rw [hs] at h
        cases h
      | some j =>
        have eq : j.succ = i := Option.some.inj (by simpa only [hs, Option.map_some] using h)
        subst i
        exact ih hs
    cases name with
    | none => exact tail h
    | some y =>
      by_cases eq : x = y
      · subst y
        have ei : (0 : Fin (Γ.length + 1)) = i :=
          Option.some.inj (by simpa [lookupSlot] using h)
        subst i
        rfl
      · exact tail (by simpa only [lookupSlot, ite_eq_right eq] using h)

theorem visible_has_names (visible : AllSlotsVisible Γ) :
    ∃ names : Fin Γ.length → ν, (∀ i, lookupSlot (names i) Γ = some i) ∧
      (∀ x i, lookupSlot x Γ = some i → names i = x) := by
  classical
  choose names correct using visible
  refine ⟨names, correct, ?_⟩
  intro x i h
  exact Option.some.inj ((slotName_of_lookupSlot (correct i)).symm.trans (slotName_of_lookupSlot h))

def reopenSubst (names : Fin Γ.length → ν) :
    (n : Nat) → Fin (Γ.length + n) → Tm ν Φ n
  | 0, i => .fv (names i)
  | n + 1, i => Tm.upSub (reopenSubst names n) i

omit [DecidableEq ν] in
theorem reopenSubst_succ (names : Fin Γ.length → ν) (n : Nat) :
    Tm.upSub (reopenSubst (Φ := Φ) names n) = reopenSubst names (n + 1) :=
  funext fun _ => rfl

/-- Change the empty name type while preserving scope and constructors. -/
def weakenNames : {n : Nat} → Tm Empty Φ n → Tm ν Φ n
  | _, .fv x => x.elim
  | _, .bv i => .bv i
  | _, .op f t => .op f (weakenNames t)
  | _, .let₁ t b => .let₁ (weakenNames t) (weakenNames b)
  | _, .unit => .unit
  | _, .pair t s => .pair (weakenNames t) (weakenNames s)
  | _, .let₂ t b => .let₂ (weakenNames t) (weakenNames b)
  | _, .inl t => .inl (weakenNames t)
  | _, .inr t => .inr (weakenNames t)
  | _, .case t l r => .case (weakenNames t) (weakenNames l) (weakenNames r)
  | _, .abort t => .abort (weakenNames t)
  | _, .iter t b => .iter (weakenNames t) (weakenNames b)

section WeakenNames

open Silmaril.Isotope.LetIter.LocallyNameless
  (Pure CoreAxiom StructuralAxiom SequencingAxiom IterationAxiom Equiv Refinement AbortSequence)

omit [DecidableEq ν] in
private theorem weakenNames_rename {n m : Nat} (rho : Fin n → Fin m) (t : Tm Empty Φ n) :
    weakenNames (ν := ν) (t.rename rho) = (weakenNames t).rename rho := by
  induction t generalizing m <;> simp_all only [Tm.rename, weakenNames]
  case fv x => exact x.elim

omit [DecidableEq ν] in
private theorem weakenNames_lift {n : Nat} (t : Tm Empty Φ n) :
    weakenNames (ν := ν) t.lift = (weakenNames t).lift :=
  weakenNames_rename Fin.succ t

omit [DecidableEq ν] in
private theorem weakenNames_upSub {n m : Nat} (sub : Fin n → Tm Empty Φ m) :
    (fun i => weakenNames (ν := ν) (Tm.upSub sub i)) = Tm.upSub (fun i => weakenNames (sub i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Tm.upSub, Fin.cases_succ, weakenNames_lift]

omit [DecidableEq ν] in
private theorem weakenNames_bsubst {n m : Nat} (sub : Fin n → Tm Empty Φ m) (t : Tm Empty Φ n) :
    weakenNames (ν := ν) (t.bsubst sub) = (weakenNames t).bsubst (fun i => weakenNames (sub i)) := by
  induction t generalizing m <;> simp_all only [Tm.bsubst, weakenNames, weakenNames_upSub]
  case fv x => exact x.elim

omit [DecidableEq ν] in
private theorem weakenNames_instantiate {n : Nat} (b : Tm Empty Φ (n + 1)) (a : Tm Empty Φ n) :
    weakenNames (ν := ν) (b.instantiate a) = (weakenNames b).instantiate (weakenNames a) := by
  unfold Tm.instantiate
  rw [weakenNames_bsubst]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

variable {ε : Type r} [HasEff Φ ε] {pe : ε}

omit [DecidableEq ν] in
private theorem weakenNames_pure {n : Nat} {t : Tm Empty Φ n} (h : Pure pe t) :
    Pure pe (weakenNames (ν := ν) t) := by
  induction h with
  | fv => rename_i x; exact x.elim
  | bv => exact .bv
  | op hf _ ih => exact .op hf ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih

omit [DecidableEq ν] in
private theorem weakenNames_core {n : Nat} {a b : Tm Empty Φ n} (h : CoreAxiom pe a b) :
    CoreAxiom pe (weakenNames (ν := ν) a) (weakenNames b) := by
  cases h with
  | structural h =>
    apply CoreAxiom.structural
    cases h with
    | letBeta hp => simpa only [weakenNames, weakenNames_instantiate] using
        (StructuralAxiom.letBeta (weakenNames_pure (ν := ν) hp))
    | letEta => exact .letEta _
    | unitEta => exact .unitEta _
    | pairBeta => simpa only [weakenNames, weakenNames_lift] using
        (StructuralAxiom.pairBeta (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _) (weakenNames _))
    | pairEta => exact .pairEta _
    | caseBetaL => exact .caseBetaL _ _ _
    | caseBetaR => exact .caseBetaR _ _ _
    | caseEta => exact .caseEta _
    | emptyInitial => exact .emptyInitial _ _ _
  | sequencing h =>
    apply CoreAxiom.sequencing
    cases h with
    | bindOp => simpa only [weakenNames, Tm.underBinder, weakenNames_rename] using
        (SequencingAxiom.bindOp (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _))
    | bindLet => simpa only [weakenNames, Tm.underBinder, weakenNames_rename] using
        (SequencingAxiom.bindLet (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _) (weakenNames _))
    | bindLetPair => simpa only [weakenNames, Tm.underBinder, weakenNames_rename] using
        (SequencingAxiom.bindLetPair (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _) (weakenNames _))
    | bindLetCase => simpa only [weakenNames, Tm.underBinder, weakenNames_rename] using
        (SequencingAxiom.bindLetCase (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _) (weakenNames _) (weakenNames _))
    | bindPair => simpa only [weakenNames, Tm.underTwoBinders, weakenNames_rename] using
        (SequencingAxiom.bindPair (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _))
    | bindCase => simpa only [weakenNames, Tm.underBinder, weakenNames_rename] using
        (SequencingAxiom.bindCase (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _) (weakenNames _))
  | iteration h =>
    apply CoreAxiom.iteration
    cases h with
    | fixpoint => simpa only [weakenNames, Tm.underBinder, weakenNames_rename] using
        (IterationAxiom.fixpoint (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _))
    | naturality => simpa only [weakenNames, Tm.underBinder, weakenNames_rename] using
        (IterationAxiom.naturality (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _) (weakenNames _))
    | codiagonal => simpa only [weakenNames, Tm.underBinder, weakenNames_rename] using
        (IterationAxiom.codiagonal (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _))
    | iterBind => simpa only [weakenNames, Tm.underBinder, weakenNames_rename] using
        (IterationAxiom.iterBind (pureEff := pe) (weakenNames (ν := ν) _) (weakenNames _))

variable [TypeFormers τ] [HasTy Φ τ]

omit [HasEff Φ ε] in
private theorem weakenNames_hasType {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (h : HasType Φ (Ctx.nil : Ctx Empty τ) β t A) : HasType Φ Γ β (weakenNames t) A := by
  induction h with
  | @fv _ _ x _ _ => exact x.elim
  | bv => exact .bv
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | iter _ _ iha ihb => exact .iter iha ihb

private theorem weakenNames_equiv {n : Nat} {β : BoundCtx τ n} {a b : Tm Empty Φ n} {A : τ}
    (h : Equiv pe (Ctx.nil : Ctx Empty τ) β a b A) : Equiv pe Γ β (weakenNames a) (weakenNames b) A := by
  induction h with
  | refl h => exact .refl (weakenNames_hasType h)
  | symm _ ih => exact .symm ih
  | trans _ _ iha ihb => exact .trans iha ihb
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | iter _ _ iha ihb => exact .iter iha ihb
  | ax law ha hb => exact .ax (weakenNames_core law) (weakenNames_hasType ha) (weakenNames_hasType hb)
  | uniformity ha hh hp hb hb' _ ih =>
    apply Equiv.uniformity (weakenNames_hasType ha) (weakenNames_hasType hh) (weakenNames_pure hp)
      (weakenNames_hasType hb) (weakenNames_hasType hb')
    simpa only [weakenNames, weakenNames_instantiate, Tm.underBinder, weakenNames_rename] using ih

/-- A term with no free names admits any free-name context at the same bound scope. -/
theorem weakenNames_abortEquiv {n : Nat} {β : BoundCtx τ n} {a b : Tm Empty Φ n} {A : τ}
    (h : AbortEquiv pe (Ctx.nil : Ctx Empty τ) β a b A) : AbortEquiv pe Γ β (weakenNames a) (weakenNames b) A := by
  induction h with
  | equiv h => exact .equiv (weakenNames_equiv h)
  | primitive law ha hb =>
    cases law with
    | sequence h =>
      exact .primitive (AbortSequence.sequence (weakenNames_hasType h))
        (weakenNames_hasType ha) (weakenNames_hasType hb)
    | unsequence h =>
      exact .primitive (AbortSequence.unsequence (weakenNames_hasType h))
        (weakenNames_hasType ha) (weakenNames_hasType hb)
  | trans _ _ iha ihb => exact .trans iha ihb
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | iter _ _ iha ihb => exact .iter iha ihb

end WeakenNames

omit [DecidableEq ν] in
theorem reopenSubst_free (names : Fin Γ.length → ν) (i : Fin Γ.length) (n : Nat) :
    (reopenSubst (Φ := Φ) names n) (freeIndex i n) = .fv (names i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [reopenSubst, freeIndex, Tm.upSub, Fin.cases_succ, ih, Tm.lift, Tm.rename]

omit [DecidableEq ν] in
theorem reopenSubst_bound (names : Fin Γ.length → ν) (n : Nat) (i : Fin n) :
    (reopenSubst (Φ := Φ) names n) (boundIndex Γ.length i) = .bv i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) i
    simp only [reopenSubst, boundIndex, Fin.cases_succ, Tm.upSub, ih, Tm.lift, Tm.rename]

variable [TypeFormers τ] [HasTy Φ τ]

/-- Slot-wise reopening recovers the original typed term when the selected
name is the name of every visible slot that was used. -/
theorem reopen_close (names : Fin Γ.length → ν)
    (correct : ∀ x i, lookupSlot x Γ = some i → names i = x)
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) :
    Tm.bsubst (reopenSubst names n) (weakenNames (closeTm Γ t)) = t := by
  induction h with
  | @fv n β x A h =>
    have h' := (lookupSlot_eq_lookup x Γ).trans h
    cases hs : lookupSlot x Γ with
    | none => simp [hs] at h'
    | some i => simp [closeTm, hs, weakenNames, Tm.bsubst, reopenSubst_free, correct x i hs]
  | bv => simp [closeTm, weakenNames, Tm.bsubst, reopenSubst_bound]
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [closeTm, weakenNames, Tm.bsubst, ih]
  | unit => rfl
  | let₁ _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ | iter _ _ ih₁ ih₂ =>
    simp only [closeTm, weakenNames, Tm.bsubst, reopenSubst_succ, ih₁, ih₂]
  | pair _ _ ih₁ ih₂ => simp only [closeTm, weakenNames, Tm.bsubst, ih₁, ih₂]
  | case _ _ _ ih₁ ih₂ ih₃ =>
    simp only [closeTm, weakenNames, Tm.bsubst, reopenSubst_succ, ih₁, ih₂, ih₃]

variable {ε : Type r} [HasEff Φ ε]

theorem reopenSubst_pureTyped (pe : ε) (names : Fin Γ.length → ν)
    (slots : ∀ i, lookupSlot (names i) Γ = some i) {n : Nat} (β : BoundCtx τ n) :
    PureTypedSubst (Φ := Φ) pe Γ (prepend (freeSlots Γ) β) β (reopenSubst names n) := by
  induction β with
  | nil =>
    refine ⟨fun i => .fv ?_, fun _ => .fv⟩
    have h := lookupSlot_eq_lookup (names i) Γ
    rw [slots i] at h
    exact h.symm
  | snoc β A ih => exact ih.up A

/-- Reopen an all-bound repaired equation by pure typed substitution. -/
public theorem reopen_abortEquiv (pe : ε) (visible : AllSlotsVisible Γ)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (da : HasType Φ Γ β a A) (db : HasType Φ Γ β b A)
    (h : AbortEquiv pe (Ctx.nil : Ctx Empty τ) (prepend (freeSlots Γ) β)
      (closeTm Γ a) (closeTm Γ b) A) :
    AbortEquiv pe Γ β a b A := by
  obtain ⟨names, slots, correct⟩ := visible_has_names visible
  have opened := (weakenNames_abortEquiv h).bsubst (reopenSubst_pureTyped pe names slots β)
  rw [reopen_close names correct da, reopen_close names correct db] at opened
  exact opened

end Reopening

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.NamedContext.ReopeningProofs
