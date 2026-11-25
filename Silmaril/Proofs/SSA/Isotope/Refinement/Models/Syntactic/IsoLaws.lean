module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Reduction
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Coproducts

/-! # Native equations for the structural arrows -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Inserting a discarded pure unit computation preserves an input. -/
def unitThenArrow (A : τ) : Arrow (Φ := Φ) (ε := ε) F A A :=
  ⟨.let₁ .unit (.bv 1), ⟨.let₁ (inputSplit A).symm (zeroUnitDeriv A ⊤)
    (unitLiftDeriv (identityDeriv A ⊤))⟩⟩

theorem unitThen_equates (A : τ) :
    Equates (ε := ε) F R (input A) (unitThenArrow (ε := ε) (Φ := Φ) (F := F) A).val (.bv 0) A := by
  have h := pureBeta (R := R) (inputSplit A) (zeroUnitDeriv A (⊥ : ε))
    (unitLiftDeriv (identityDeriv (F := F) (Φ := Φ) A (⊤ : ε)))
    (by rw [TypeQuantity.unit_quantity, zeroInput_linearity])
    (show WellTyped (ε := ε) F (input A) (.bv 0) A from ⟨identityDeriv A ⊤⟩)
  exact h

/-- A parameter of unit type equals the canonical unit value. -/
theorem unitVariable_equates :
    Equates (ε := ε) F R (input (Silmaril.unit : τ)) (.bv 0 : Term Φ 1) .unit Silmaril.unit := by
  have du : HasType F (input (Silmaril.unit : τ)) (⊤ : ε) (.unit : Term Φ 1) Silmaril.unit :=
    discardDeriv Silmaril.unit (by rw [TypeQuantity.unit_quantity]; exact le_top) ⊤
  have db : HasType F ((QCtx.nil.snoc (Silmaril.unit : τ) .zero).snoc Silmaril.unit)
      (⊤ : ε) (.unit : Term Φ 2) Silmaril.unit := by
    apply HasType.unit
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [QCtx.effective, QCtx.snoc_zero, Usage.effective, Usage.used_mul_used,
        TypeQuantity.unit_quantity, inf_top_eq, Usage.zero_le_used]
      exact le_top
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      exact le_rfl
  have hp := pureBeta (R := R) (inputSplit (Silmaril.unit : τ)).symm
    (identityDeriv (F := F) (Φ := Φ) Silmaril.unit (⊥ : ε)) db
    (by rw [input_linearity]) ⟨du⟩
  have he := Equates.ofAxiom (R := R) (.term (identityDeriv (F := F) (Φ := Φ) Silmaril.unit (⊤ : ε)))
    (show WellTyped (ε := ε) F (input (Silmaril.unit : τ)) (.let₁ (.bv 0) .unit) Silmaril.unit from
      ⟨.let₁ (inputSplit _) (identityDeriv _ _) db⟩)
    (show WellTyped (ε := ε) F (input (Silmaril.unit : τ)) (.bv 0) Silmaril.unit from
      ⟨identityDeriv _ _⟩)
  exact he.symm.trans hp

/-- Product beta expresses the retraction of the right unitor. -/
def rightUnitBetaArrow (A : τ) : Arrow (Φ := Φ) (ε := ε) F A A :=
  ⟨.let₂ (.pair (.bv 0) .unit) (.bv 1),
    ⟨.let₂ (inputSplit A) (rightUnitInvDeriv A ⊤) (rightUnitBodyDeriv A A ⊤)⟩⟩

theorem rightUnitInv_rightUnit_equates (A : τ) :
    Equates (ε := ε) F R (input A)
      (composeArrow (rightUnitInvArrow (ε := ε) (Φ := Φ) (F := F) A) (rightUnitArrow A)).val
      (.bv 0) A := by
  apply Equates.trans (b := (rightUnitBetaArrow (ε := ε) (Φ := Φ) (F := F) A).val)
  · exact (Equates.ofAxiom
      (.pairBind (inputSplit A) (rightUnitInvDeriv A (⊤ : ε)) (rightUnitBodyDeriv A A ⊤))
      (rightUnitBetaArrow (ε := ε) (Φ := Φ) (F := F) A).property
      (composeArrow (rightUnitInvArrow (ε := ε) (Φ := Φ) (F := F) A) (rightUnitArrow A)).property).symm
  · apply Equates.trans (b := (composeArrow (identityArrow A) (unitThenArrow (F := F) (ε := ε) (Φ := Φ) A)).val)
    · exact Equates.ofAxiom
        (.pairBeta (inputSplit A).symm (inputSplit A).symm
          (identityDeriv A (⊤ : ε)) (zeroUnitDeriv A ⊤) (rightUnitBodyDeriv A A ⊤))
        (rightUnitBetaArrow (ε := ε) (Φ := Φ) (F := F) A).property
        (composeArrow (identityArrow A) (unitThenArrow (F := F) (ε := ε) (Φ := Φ) A)).property
    · exact (identity_compose_equates R (unitThenArrow (F := F) (ε := ε) (Φ := Φ) A)).trans
        (unitThen_equates A)

@[simp] theorem rightUnitInv_rightUnit (hR : R.RenamingClosed) (A : τ) :
    compose (ε := ε) (F := F) (R := R) hR (rightUnitInv A) (rightUnit A) = identity A :=
  Quotient.sound (rightUnitInv_rightUnit_equates A)


/-- A discarded original unit component can be replaced by the canonical value. -/
theorem rightUnitBody_equates (hR : R.RenamingClosed) (P A : τ) :
    Equates (ε := ε) F R (pairContext P A Silmaril.unit)
      (.pair (.bv 1) .unit : Term Φ 3) (.pair (.bv 1) (.bv 0)) (product A Silmaril.unit) := by
  apply Equates.pair (pairSplit P A Silmaril.unit)
    (Equates.refl ⟨leftParameter _ _ _ (⊤ : ε)⟩)
  exact (unitVariable_equates (F := F) (R := R) (Φ := Φ) (ε := ε)).symm.rename _
    (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl) hR

/-- The other right-unitor inverse law follows from pure beta and product eta. -/
theorem rightUnit_rightUnitInv_equates (hR : R.RenamingClosed) (A : τ) :
    Equates (ε := ε) F R (input (product A Silmaril.unit))
      (composeArrow (rightUnitArrow (ε := ε) (Φ := Φ) (F := F) A) (rightUnitInvArrow A)).val
      (.bv 0) (product A Silmaril.unit) := by
  let P := product A Silmaril.unit
  have du : HasType F (pairRightContext P A Silmaril.unit) (⊤ : ε)
      (.unit : Term Φ 3) Silmaril.unit :=
    (discardDeriv (F := F) (Φ := Φ) Silmaril.unit
      (by rw [TypeQuantity.unit_quantity]; exact le_top) (⊤ : ε)).rename _
      (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl)
  have dout : WellTyped (ε := ε) F (pairContext P A Silmaril.unit)
      (.pair (.bv 1) .unit : Term Φ 3) P :=
    ⟨.pair (pairSplit P A Silmaril.unit) (leftParameter _ _ _ _) du⟩
  have hq : quantity A ≤ (pairContext P A Silmaril.unit).linearity := by
    simp only [pairContext, QCtx.linearity_snoc, Usage.linearity_used,
      Usage.linearity_zero, QCtx.linearity_nil, TypeQuantity.unit_quantity, inf_top_eq,
      top_inf_eq]
    exact le_inf le_rfl le_top
  have hb : Equates (ε := ε) F R (pairContext P A Silmaril.unit)
      (.let₁ (.bv 1) (.pair (.bv 0) .unit) : Term Φ 3) (.pair (.bv 1) .unit) P := by
    exact pureBeta
      (((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc (.left (.used ⊤)))
      (rightUnitBodyDeriv P A (⊥ : ε))
      ((rightUnitInvDeriv (F := F) (Φ := Φ) A (⊤ : ε)).rename _
        (.cons (.skip (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl) le_rfl))
      hq dout
  let mid : Arrow (Φ := Φ) (ε := ε) F P P :=
    ⟨.let₂ (.bv 0) (.let₁ (.bv 1) (.pair (.bv 0) .unit)), by
      obtain ⟨d⟩ := hb.1.wellTyped.1
      exact ⟨.let₂ (inputSplit _) (identityDeriv _ _) d⟩⟩
  apply Equates.trans (b := mid.val)
  · exact Equates.ofAxiom
      (.letLetPair (inputSplit P) (QCtx.Split.nil.snoc (.left .zero))
        (identityDeriv P (⊤ : ε)) (rightUnitBodyDeriv P A ⊤)
        ((rightUnitInvDeriv (F := F) (Φ := Φ) A (⊤ : ε)).rename _
          ((QCtx.Weakening.insertZero QCtx.nil P).up A)))
      (composeArrow (rightUnitArrow (ε := ε) (Φ := Φ) (F := F) A) (rightUnitInvArrow A)).property
      mid.property
  · apply Equates.trans (b := .let₂ (.bv 0) (.pair (.bv 1) (.bv 0)))
    · exact Equates.let₂ (inputSplit P) (Equates.refl ⟨identityDeriv P (⊤ : ε)⟩)
        (hb.trans (rightUnitBody_equates hR P A))
    · exact Equates.ofAxiom (.pairEta (identityDeriv P (⊤ : ε)))
        ⟨.let₂ (inputSplit P) (identityDeriv P ⊤)
          (.pair (pairSplit P A Silmaril.unit) (leftParameter _ _ _ _) (rightParameter _ _ _ _))⟩
        ⟨identityDeriv P ⊤⟩

@[simp] theorem rightUnit_rightUnitInv (hR : R.RenamingClosed) (A : τ) :
    compose (ε := ε) (F := F) (R := R) hR (rightUnit A) (rightUnitInv A) =
      identity (product A Silmaril.unit) :=
  Quotient.sound (rightUnit_rightUnitInv_equates hR A)


/-- The canonical right unitor is an actual isomorphism in the native quotient. -/
def rightUnitIso (hR : R.RenamingClosed) (A : τ) :
    letI := category (ε := ε) F R hR
    CategoryTheory.Iso (product A Silmaril.unit) A := by
  letI := category (ε := ε) F R hR
  exact ⟨rightUnit A, rightUnitInv A, rightUnit_rightUnitInv hR A,
    rightUnitInv_rightUnit hR A⟩

/-- Replacing the left unit component respects the quantitative split. -/
theorem leftUnitBody_equates (hR : R.RenamingClosed) (P A : τ) :
    Equates (ε := ε) F R (pairContext P Silmaril.unit A)
      (.pair .unit (.bv 0) : Term Φ 3) (.pair (.bv 1) (.bv 0)) (product Silmaril.unit A) := by
  apply Equates.pair (pairSplit P Silmaril.unit A) _
    (Equates.refl ⟨rightParameter _ _ _ (⊤ : ε)⟩)
  exact (unitVariable_equates (F := F) (R := R) (Φ := Φ) (ε := ε)).symm.rename _
    (.skip (.cons (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl) hR

theorem leftUnit_leftUnitInv_equates (hR : R.RenamingClosed) (A : τ) :
    Equates (ε := ε) F R (input (product Silmaril.unit A))
      (composeArrow (leftUnitArrow (ε := ε) (Φ := Φ) (F := F) A) (leftUnitInvArrow A)).val
      (.bv 0) (product Silmaril.unit A) := by
  let P := product Silmaril.unit A
  have du : HasType F (pairLeftContext P Silmaril.unit A) (⊤ : ε)
      (.unit : Term Φ 3) Silmaril.unit :=
    (discardDeriv (F := F) (Φ := Φ) Silmaril.unit
      (by rw [TypeQuantity.unit_quantity]; exact le_top) (⊤ : ε)).rename _
      (.skip (.cons (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl)
  have dout : WellTyped (ε := ε) F (pairContext P Silmaril.unit A)
      (.pair .unit (.bv 0) : Term Φ 3) P :=
    ⟨.pair (pairSplit P Silmaril.unit A) du (rightParameter _ _ _ _)⟩
  have hq : quantity A ≤ (pairContext P Silmaril.unit A).linearity := by
    simp only [pairContext, QCtx.linearity_snoc, Usage.linearity_used,
      Usage.linearity_zero, QCtx.linearity_nil, TypeQuantity.unit_quantity, inf_top_eq,
      top_inf_eq]
    exact le_inf le_rfl le_top
  have hb : Equates (ε := ε) F R (pairContext P Silmaril.unit A)
      (.let₁ (.bv 0) (.pair .unit (.bv 0)) : Term Φ 3) (.pair .unit (.bv 0)) P := by
    exact pureBeta
      (((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc (.left (.used ⊤)))
      (leftUnitBodyDeriv P A (⊥ : ε))
      ((leftUnitInvDeriv (F := F) (Φ := Φ) A (⊤ : ε)).rename _
        (.cons (.skip (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl) le_rfl))
      hq dout
  let mid : Arrow (Φ := Φ) (ε := ε) F P P :=
    ⟨.let₂ (.bv 0) (.let₁ (.bv 0) (.pair .unit (.bv 0))), by
      obtain ⟨d⟩ := hb.1.wellTyped.1
      exact ⟨.let₂ (inputSplit _) (identityDeriv _ _) d⟩⟩
  apply Equates.trans (b := mid.val)
  · exact Equates.ofAxiom
      (.letLetPair (inputSplit P) (QCtx.Split.nil.snoc (.left .zero))
        (identityDeriv P (⊤ : ε)) (leftUnitBodyDeriv P A ⊤)
        ((leftUnitInvDeriv (F := F) (Φ := Φ) A (⊤ : ε)).rename _
          ((QCtx.Weakening.insertZero QCtx.nil P).up A)))
      (composeArrow (leftUnitArrow (ε := ε) (Φ := Φ) (F := F) A) (leftUnitInvArrow A)).property
      mid.property
  · apply Equates.trans (b := .let₂ (.bv 0) (.pair (.bv 1) (.bv 0)))
    · exact Equates.let₂ (inputSplit P) (Equates.refl ⟨identityDeriv P (⊤ : ε)⟩)
        (hb.trans (leftUnitBody_equates hR P A))
    · exact Equates.ofAxiom (.pairEta (identityDeriv P (⊤ : ε)))
        ⟨.let₂ (inputSplit P) (identityDeriv P ⊤)
          (.pair (pairSplit P Silmaril.unit A) (leftParameter _ _ _ _) (rightParameter _ _ _ _))⟩
        ⟨identityDeriv P ⊤⟩

@[simp] theorem leftUnit_leftUnitInv (hR : R.RenamingClosed) (A : τ) :
    compose (ε := ε) (F := F) (R := R) hR (leftUnit A) (leftUnitInv A) =
      identity (product Silmaril.unit A) :=
  Quotient.sound (leftUnit_leftUnitInv_equates hR A)

/-- Product beta expresses the retraction of the left unitor. -/
def leftUnitBetaArrow (A : τ) : Arrow (Φ := Φ) (ε := ε) F A A :=
  ⟨.let₂ (.pair .unit (.bv 0)) (.bv 0),
    ⟨.let₂ (inputSplit A) (leftUnitInvDeriv A ⊤) (leftUnitBodyDeriv A A ⊤)⟩⟩

theorem leftUnitInv_leftUnit_equates (hR : R.RenamingClosed) (A : τ) :
    Equates (ε := ε) F R (input A)
      (composeArrow (leftUnitInvArrow (ε := ε) (Φ := Φ) (F := F) A) (leftUnitArrow A)).val
      (.bv 0) A := by
  have hv : Equates (ε := ε) F R ((input A).snoc Silmaril.unit)
      (.let₁ (.bv 1) (.bv 0) : Term Φ 2) (.bv 1) A :=
    (compose_identity_equates R (identityArrow (F := F) (Φ := Φ) (ε := ε) A)).rename Fin.succ
      (.skip (.refl _) (by
        simp only [Usage.effective, Usage.used_mul_used, TypeQuantity.unit_quantity,
          inf_top_eq, Usage.zero_le_used]
        exact le_top)) hR
  let mid : Arrow (Φ := Φ) (ε := ε) F A A :=
    ⟨.let₁ .unit (.let₁ (.bv 1) (.bv 0)), by
      obtain ⟨d⟩ := hv.1.wellTyped.1
      exact ⟨.let₁ (inputSplit A).symm (zeroUnitDeriv A ⊤) d⟩⟩
  apply Equates.trans (b := (leftUnitBetaArrow (ε := ε) (Φ := Φ) (F := F) A).val)
  · exact (Equates.ofAxiom
      (.pairBind (inputSplit A) (leftUnitInvDeriv A (⊤ : ε)) (leftUnitBodyDeriv A A ⊤))
      (leftUnitBetaArrow (ε := ε) (Φ := Φ) (F := F) A).property
      (composeArrow (leftUnitInvArrow (ε := ε) (Φ := Φ) (F := F) A) (leftUnitArrow A)).property).symm
  · apply Equates.trans (b := mid.val)
    · exact Equates.ofAxiom
        (.pairBeta (inputSplit A).symm (inputSplit A)
          (zeroUnitDeriv A (⊤ : ε)) (identityDeriv A ⊤) (leftUnitBodyDeriv A A ⊤))
        (leftUnitBetaArrow (ε := ε) (Φ := Φ) (F := F) A).property mid.property
    · exact (Equates.let₁ (inputSplit A).symm (Equates.refl ⟨zeroUnitDeriv A (⊤ : ε)⟩)
        hv).trans (unitThen_equates A)

@[simp] theorem leftUnitInv_leftUnit (hR : R.RenamingClosed) (A : τ) :
    compose (ε := ε) (F := F) (R := R) hR (leftUnitInv A) (leftUnit A) = identity A :=
  Quotient.sound (leftUnitInv_leftUnit_equates hR A)

/-- The canonical left unitor is an actual isomorphism in the native quotient. -/
def leftUnitIso (hR : R.RenamingClosed) (A : τ) :
    letI := category (ε := ε) F R hR
    CategoryTheory.Iso (product Silmaril.unit A) A := by
  letI := category (ε := ε) F R hR
  exact ⟨leftUnit A, leftUnitInv A, leftUnit_leftUnitInv hR A,
    leftUnitInv_leftUnit hR A⟩

end Silmaril.Isotope.Refinement.Models.Syntactic
