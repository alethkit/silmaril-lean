module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheorySubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheoryTyping

/-! # Typed record destructuring and its constructor-pair retraction -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructure

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.InputDestructure

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

private theorem retainedAt (Γ : VCtx τ) {Δ : VCtx τ} {i : Nat} {A : τ} (h : At Δ i A) :
    At (expanded Γ Δ) (retained Γ i) A := by
  induction Γ generalizing Δ i with
  | nil => exact h
  | cons B Γ ih => exact ih (Δ := B :: packedInputType Γ :: Δ) (i := i + 2) h

theorem fieldRen (Γ Δ : VCtx τ) : Ren Γ (expanded Γ Δ) (field Γ) := by
  intro i A hi
  induction Γ generalizing Δ i with
  | nil => simp [At] at hi
  | cons B Γ ih =>
    cases i with
    | zero =>
      have e : B = A := Option.some.inj hi
      subst A
      exact retainedAt Γ (Δ := B :: packedInputType Γ :: Δ) (i := 0) rfl
    | succ i => exact ih (Δ := B :: packedInputType Γ :: Δ) (i := i) hi

variable [Silmaril.HasTy Φ τ]

private theorem split_typed (Γ : VCtx τ) {Δ : VCtx τ} {i : Nat} {r : Region Φ} {L : LCtx τ}
    (hi : At Δ i (packedInputType Γ)) (hr : Region.HasType (expanded Γ Δ) r L) :
    Region.HasType Δ (split Γ i r) L := by
  induction Γ generalizing Δ i with
  | nil => exact hr
  | cons A Γ ih =>
    exact .let₂ (.var hi) (ih (Δ := A :: packedInputType Γ :: Δ) (i := 1) rfl hr)

theorem pack_typed {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ} (hr : Region.HasType Γ r L) :
    Region.HasType [packedInputType Γ] (r.packInputsDestructure Γ) L :=
  split_typed Γ rfl (hr.renameVars (fieldRen Γ [packedInputType Γ]))

private theorem renameBranches {Γ Δ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {ρ : Nat → Nat} (hr : ValueBranches Γ r L) (hρ : Ren Γ Δ ρ) :
    ValueBranches Δ (r.renameVars ρ) L := by
  induction hr generalizing Δ ρ with
  | br hl ha => exact .br hl (branchValue_rename ha hρ)
  | let₁ ha _ ih => exact .let₁ (ha.rename hρ) (ih (hρ.lift _))
  | let₂ ha _ ih => exact .let₂ (ha.rename hρ) (ih ((hρ.lift _).lift _))
  | case ha _ _ ihl ihr => exact .case (ha.rename hρ) (ihl (hρ.lift _)) (ihr (hρ.lift _))
  | cfg R _ _ ihe ihb => exact .cfg R (ihe hρ) (fun i => ihb i (hρ.lift _))

theorem split_valueBranches (Γ : VCtx τ) {Δ : VCtx τ} {i : Nat} {r : Region Φ}
    {L : LCtx τ} (hi : At Δ i (packedInputType Γ)) (hr : ValueBranches (expanded Γ Δ) r L) :
    ValueBranches Δ (split Γ i r) L := by
  induction Γ generalizing Δ i with
  | nil => exact hr
  | cons A Γ ih =>
    exact .let₂ (.var hi) (ih (Δ := A :: packedInputType Γ :: Δ) (i := 1) rfl hr)

theorem pack_valueBranches {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ} (hr : ValueBranches Γ r L) :
    ValueBranches [packedInputType Γ] (r.packInputsDestructure Γ) L :=
  split_valueBranches Γ rfl (renameBranches hr (fieldRen Γ [packedInputType Γ]))

private theorem split_congr (Γ : VCtx τ) {Δ : VCtx τ} {i : Nat} {r s : Region Φ}
    {L : LCtx τ} (hi : At Δ i (packedInputType Γ)) (h : CfgEta.Eqv (expanded Γ Δ) r s L) :
    CfgEta.Eqv Δ (split Γ i r) (split Γ i s) L := by
  induction Γ generalizing Δ i with
  | nil => exact h
  | cons A Γ ih =>
    exact .let₂ (.var hi) (ih (Δ := A :: packedInputType Γ :: Δ) (i := 1) rfl h)

theorem pack_congr {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : CfgEta.Eqv Γ r s L) :
    CfgEta.Eqv [packedInputType Γ] (r.packInputsDestructure Γ) (s.packInputsDestructure Γ) L :=
  split_congr Γ rfl (h.renameVars (fieldRen Γ [packedInputType Γ]))

private def KeepsVariables (Γ : VCtx τ) (θ : Nat → Tm Φ) : Prop :=
  ∀ ⦃i A⦄, At Γ i A → θ i = .var i

omit [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ] in
private theorem KeepsVariables.lift {Γ : VCtx τ} {θ : Nat → Tm Φ}
    (h : KeepsVariables Γ θ) (A : τ) : KeepsVariables (A :: Γ) (Tm.liftSubst θ) := by
  intro i B hi
  cases i with
  | zero => rfl
  | succ i =>
    change (θ i).rename Nat.succ = .var (i + 1)
    rw [h (show At Γ i B from hi)]
    rfl

private theorem tm_subst_keeps {Γ : VCtx τ} {A : τ} {a : Tm Φ} (h : Tm.HasType Γ a A)
    {θ : Nat → Tm Φ} (hθ : KeepsVariables Γ θ) : a.subst θ = a := by
  induction h generalizing θ with
  | var hi => exact hθ hi
  | unit => rfl
  | op _ ih => exact congrArg (Tm.op _) (ih hθ)
  | pair _ _ iha ihb => exact congrArg₂ Tm.pair (iha hθ) (ihb hθ)
  | let₁ _ _ iha ihb => exact congrArg₂ Tm.let₁ (iha hθ) (ihb (hθ.lift _))
  | let₂ _ _ iha ihb => exact congrArg₂ Tm.let₂ (iha hθ) (ihb ((hθ.lift _).lift _))
  | inl _ ih => exact congrArg Tm.inl (ih hθ)
  | inr _ ih => exact congrArg Tm.inr (ih hθ)
  | abort _ ih => exact congrArg Tm.abort (ih hθ)
  | case _ _ _ iha ihl ihr =>
    simp only [Tm.subst, iha hθ, ihl (hθ.lift _), ihr (hθ.lift _)]

private theorem region_subst_keeps {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType Γ r L) {θ : Nat → Tm Φ} (hθ : KeepsVariables Γ θ) :
    r.substVars θ = r := by
  induction hr generalizing θ with
  | br _ ha => exact congrArg (Region.br _) (tm_subst_keeps ha hθ)
  | let₁ ha _ ih => exact congrArg₂ Region.let₁ (tm_subst_keeps ha hθ) (ih (hθ.lift _))
  | let₂ ha _ ih => exact congrArg₂ Region.let₂ (tm_subst_keeps ha hθ) (ih ((hθ.lift _).lift _))
  | case ha _ _ ihl ihr =>
    simp only [Region.substVars, tm_subst_keeps ha hθ, ihl (hθ.lift _), ihr (hθ.lift _)]
  | cfg R _ _ ihe ihb =>
    exact congrArg₂ (fun e bs => Region.cfg e _ bs) (ihe hθ) (funext fun i => ihb i (hθ.lift (R i)))

theorem singleton_subst_keeps {P : τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType [P] r L) {θ : Nat → Tm Φ} (h : θ 0 = .var 0) :
    r.substVars θ = r := by
  apply region_subst_keeps hr
  intro i A hi
  cases i with
  | zero => exact h
  | succ i => simp [At] at hi

private def Values (Δ Ξ : VCtx τ) (θ : Nat → Tm Φ) : Prop :=
  ∀ ⦃i A⦄, At Δ i A → Tm.BranchValue Ξ (θ i) A

private def packet (Γ : VCtx τ) (σ : Nat → Tm Φ) : Tm Φ :=
  (packedInputValue Γ).subst σ

omit [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ] in
private theorem packet_cons (A : τ) (Γ : VCtx τ) (σ : Nat → Tm Φ) :
    packet (A :: Γ) σ = .pair (packet Γ (σ ∘ Nat.succ)) (σ 0) := by
  simp only [packet, packedInputValue, Tm.subst, Tm.subst_rename]

omit [Silmaril.HasTy Φ τ] in
private theorem packet_value {Γ Ξ : VCtx τ} {σ : Nat → Tm Φ} (h : Values Γ Ξ σ) :
    Tm.BranchValue Ξ (packet Γ σ) (packedInputType Γ) :=
  branchValue_subst (packedInputValue_branchValue Γ) h

omit [Silmaril.HasTy Φ τ] in
private theorem cons_values {Δ Ξ : VCtx τ} {θ : Nat → Tm Φ} {a : Tm Φ} {A : τ}
    (hθ : Values Δ Ξ θ) (ha : Tm.BranchValue Ξ a A) :
    Values (A :: Δ) Ξ (Tm.consSubst a θ) := by
  intro i B hi
  cases i with
  | zero =>
    have h : A = B := Option.some.inj hi
    subst B
    exact ha
  | succ i => exact hθ (show At Δ i B from hi)

omit [Silmaril.HasTy Φ τ] in
private theorem drop_value {Γ Ξ : VCtx τ} {A : τ} {σ : Nat → Tm Φ}
    (hσ : Values (A :: Γ) Ξ σ) : Values Γ Ξ (σ ∘ Nat.succ) :=
  fun i T hi => hσ (i := i + 1) (A := T) hi

/-- The final simultaneous substitution induced by all constructor splits.
It stores the payload and the tail packet at each pair of fresh slots. -/
private def decoded : VCtx τ → (Nat → Tm Φ) → (Nat → Tm Φ) → Nat → Tm Φ
  | [], _, θ => θ
  | _ :: Γ, σ, θ =>
      decoded Γ (σ ∘ Nat.succ) (Tm.consSubst (σ 0) (Tm.consSubst (packet Γ (σ ∘ Nat.succ)) θ))

omit [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ] in
private theorem decoded_retained (Γ : VCtx τ) (σ θ : Nat → Tm Φ) (i : Nat) :
    decoded Γ σ θ (retained Γ i) = θ i := by
  induction Γ generalizing σ θ i with
  | nil => rfl
  | cons A Γ ih =>
    simp only [decoded, retained, ih]
    cases i <;> rfl

omit [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ] in
private theorem decoded_field (Γ : VCtx τ) (σ θ : Nat → Tm Φ)
    {i : Nat} {A : τ} (hi : At Γ i A) :
    decoded Γ σ θ (field Γ i) = σ i := by
  induction Γ generalizing σ θ i with
  | nil => simp [At] at hi
  | cons B Γ ih =>
    cases i with
    | zero => simp only [decoded, field, decoded_retained, Tm.consSubst]
    | succ i =>
      exact ih (σ ∘ Nat.succ)
        (Tm.consSubst (σ 0) (Tm.consSubst (packet Γ (σ ∘ Nat.succ)) θ)) (i := i)
        (show At Γ i A from hi)

private theorem lift_two_cancel (θ : Nat → Tm Φ) (a b : Tm Φ) :
    (fun i => (Tm.liftSubst (Tm.liftSubst θ) i).subst (Tm.consSubst b (Tm.singleSubst a))) =
      Tm.consSubst b (Tm.consSubst a θ) := by
  funext i
  rcases i with _ | _ | i
  · rfl
  · rfl
  · change (((θ i).rename Nat.succ).rename Nat.succ).subst
        (Tm.consSubst b (Tm.singleSubst a)) = θ i
    rw [Tm.rename_comp, Tm.subst_rename]
    exact Tm.subst_var _

/-- Contract every decoder binder using root β. The body is arbitrary, with
no restriction on local blocks or on the purity of expressions in the body. -/
private theorem contract_split (Γ : VCtx τ) {Δ Ξ : VCtx τ} {σ θ : Nat → Tm Φ}
    {i : Nat} {L : LCtx τ} {r : Region Φ}
    (hi : At Δ i (packedInputType Γ)) (hr : Region.HasType (expanded Γ Δ) r L)
    (hσ : Values Γ Ξ σ) (hθ : Values Δ Ξ θ) (he : θ i = packet Γ σ) :
    ProductBeta.Eqv Ξ ((split Γ i r).substVars θ) (r.substVars (decoded Γ σ θ)) L := by
  induction Γ generalizing Δ σ θ i with
  | nil =>
    exact ProductBeta.Eqv.cfgEta (.native (.base (.refl (hr.substVars (valuesTyped hθ)))))
  | cons A Γ ih =>
    let p := packet Γ (σ ∘ Nat.succ)
    let a := σ 0
    have hp : Tm.BranchValue Ξ p (packedInputType Γ) := packet_value (drop_value hσ)
    have ha : Tm.BranchValue Ξ a A := hσ (i := 0) rfl
    have hshape : θ i = .pair p a := he.trans (packet_cons A Γ σ)
    change ProductBeta.Eqv Ξ (.let₂ (θ i) ((split Γ 1 r).substVars (Tm.liftSubstN 2 θ)))
      (r.substVars (decoded Γ (σ ∘ Nat.succ) (Tm.consSubst a (Tm.consSubst p θ)))) L
    rw [hshape]
    have hbody := (split_typed Γ (rfl : At (A :: packedInputType Γ :: Δ) 1 (packedInputType Γ)) hr)
      |>.substVars (valuesTyped (liftValues (liftValues hθ (packedInputType Γ)) A))
    refine (ProductBeta.Eqv.ofStep (.let₂Beta hp ha hbody)).trans ?_
    rw [Region.substVars_comp, lift_two_cancel]
    exact ih (Δ := A :: packedInputType Γ :: Δ) (i := 1) rfl hr (drop_value hσ)
      (cons_values (cons_values hθ hp) ha) rfl

omit [Silmaril.HasTy Φ τ] in
private theorem packed_slot_values (Γ : VCtx τ) :
    Values [packedInputType Γ] Γ (Tm.singleSubst (packedInputValue Γ : Tm Φ)) := by
  intro i A hi
  cases i with
  | zero =>
    have e : packedInputType Γ = A := Option.some.inj hi
    subst A
    exact packedInputValue_branchValue Γ
  | succ i => simp [At] at hi

/-- The constructor-pair rule suffices for the input retraction at every
exactly typed region, without a branch-normalization premise. -/
theorem unpack_packInputsDestructure {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (hr : Region.HasType Γ r L) :
    ProductBeta.Eqv Γ ((r.packInputsDestructure Γ).unpackInputs Γ) r L := by
  let θ := Tm.singleSubst (packedInputValue Γ : Tm Φ)
  have he : θ 0 = packet Γ Tm.var := by
    change (packedInputValue Γ : Tm Φ) = (packedInputValue Γ).subst Tm.var
    rw [Tm.subst_var]
  have hp := contract_split Γ (i := 0) (rfl : At [packedInputType Γ] 0 (packedInputType Γ))
    (hr.renameVars (fieldRen Γ [packedInputType Γ])) (fun _ _ hi => .var hi)
    (packed_slot_values Γ) he
  rw [Region.substVars_renameVars] at hp
  have hs : KeepsVariables Γ (decoded Γ Tm.var θ ∘ field Γ) :=
    fun _ _ hi => decoded_field Γ Tm.var θ hi
  rw [region_subst_keeps hr hs] at hp
  exact hp

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructure
