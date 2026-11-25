module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Lift
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Coproducts

/-! # Coproduct equations in the written syntactic category -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless CategoryTheory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ} {A B C D : τ}

theorem continuation_desc (a b : Term Φ 1) :
    continuation (descTerm a b) =
      .case (.bv 0) (continuation a).underBinder (continuation b).underBinder := by
  simp only [continuation, descTerm, Tm.rename, Tm.underBinder, Tm.rename_comp]
  congr 1 <;> apply Tm.rename_congr <;> intro i <;>
    have hi : i = 0 := Fin.eq_zero i <;> subst i <;> rfl

def caseInlArrow (cap : F.HasCase) (a : Arrow (Φ := Φ) (ε := ε) F A C)
    (b : Arrow (Φ := Φ) (ε := ε) F B C) : Arrow (Φ := Φ) (ε := ε) F A C :=
  ⟨.case (.inl (.bv 0)) (continuation a.val) (continuation b.val), by
    obtain ⟨da⟩ := a.property
    obtain ⟨db⟩ := b.property
    exact ⟨.case cap (inputSplit A) (.inl cap (identityDeriv A ⊤))
      (da.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up A))
      (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up B))⟩⟩

def caseInrArrow (cap : F.HasCase) (a : Arrow (Φ := Φ) (ε := ε) F A C)
    (b : Arrow (Φ := Φ) (ε := ε) F B C) : Arrow (Φ := Φ) (ε := ε) F B C :=
  ⟨.case (.inr (.bv 0)) (continuation a.val) (continuation b.val), by
    obtain ⟨da⟩ := a.property
    obtain ⟨db⟩ := b.property
    exact ⟨.case cap (inputSplit B) (.inr cap (identityDeriv B ⊤))
      (da.rename _ ((QCtx.Weakening.insertZero QCtx.nil B).up A))
      (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil B).up B))⟩⟩

theorem inl_desc_equates (cap : F.HasCase)
    (a : Arrow (Φ := Φ) (ε := ε) F A C) (b : Arrow (Φ := Φ) (ε := ε) F B C) :
    Equates (ε := ε) F R (input A)
      (composeArrow (inlArrow cap A B) (descArrow cap a b)).val a.val C := by
  obtain ⟨da⟩ := a.property
  obtain ⟨db⟩ := b.property
  apply Equates.trans (b := (caseInlArrow cap a b).val)
  · apply Equates.symm
    apply Equates.ofAxiom _ (caseInlArrow cap a b).property
      (composeArrow (inlArrow cap A B) (descArrow cap a b)).property
    change EquationAxiom (ε := ε) F (input A)
      (.case (.inl (.bv 0)) (continuation a.val) (continuation b.val))
      (.let₁ (.inl (.bv 0)) (continuation (descTerm a.val b.val))) C
    rw [continuation_desc]
    exact .caseBind cap (inputSplit A) (.inl cap (identityDeriv A ⊤))
      (da.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up A))
      (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up B))
  · apply Equates.trans (b := (composeArrow (identityArrow A) a).val)
    · exact Equates.ofAxiom
        (.caseBetaL cap (inputSplit A) (identityDeriv A ⊤)
          (da.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up A))
          (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up B)))
        (caseInlArrow cap a b).property (composeArrow (identityArrow A) a).property
    · exact identity_compose_equates R a

theorem inr_desc_equates (cap : F.HasCase)
    (a : Arrow (Φ := Φ) (ε := ε) F A C) (b : Arrow (Φ := Φ) (ε := ε) F B C) :
    Equates (ε := ε) F R (input B)
      (composeArrow (inrArrow cap A B) (descArrow cap a b)).val b.val C := by
  obtain ⟨da⟩ := a.property
  obtain ⟨db⟩ := b.property
  apply Equates.trans (b := (caseInrArrow cap a b).val)
  · apply Equates.symm
    apply Equates.ofAxiom _ (caseInrArrow cap a b).property
      (composeArrow (inrArrow cap A B) (descArrow cap a b)).property
    change EquationAxiom (ε := ε) F (input B)
      (.case (.inr (.bv 0)) (continuation a.val) (continuation b.val))
      (.let₁ (.inr (.bv 0)) (continuation (descTerm a.val b.val))) C
    rw [continuation_desc]
    exact .caseBind cap (inputSplit B) (.inr cap (identityDeriv B ⊤))
      (da.rename _ ((QCtx.Weakening.insertZero QCtx.nil B).up A))
      (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil B).up B))
  · apply Equates.trans (b := (composeArrow (identityArrow B) b).val)
    · exact Equates.ofAxiom
        (.caseBetaR cap (inputSplit B) (identityDeriv B ⊤)
          (da.rename _ ((QCtx.Weakening.insertZero QCtx.nil B).up A))
          (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil B).up B)))
        (caseInrArrow cap a b).property (composeArrow (identityArrow B) b).property
    · exact identity_compose_equates R b

theorem desc_compose_equates (cap : F.HasCase)
    (a : Arrow (Φ := Φ) (ε := ε) F A C) (b : Arrow (Φ := Φ) (ε := ε) F B C)
    (c : Arrow (Φ := Φ) (ε := ε) F C D) :
    Equates (ε := ε) F R (input (coprod A B))
      (composeArrow (descArrow cap a b) c).val
      (descArrow cap (composeArrow a c) (composeArrow b c)).val D := by
  obtain ⟨da⟩ := a.property
  obtain ⟨db⟩ := b.property
  obtain ⟨dc⟩ := c.property
  apply Equates.ofAxiom _ (composeArrow (descArrow cap a b) c).property
    (descArrow cap (composeArrow a c) (composeArrow b c)).property
  change EquationAxiom (ε := ε) F (input (coprod A B))
    (.let₁ (.case (.bv 0) (continuation a.val) (continuation b.val)) (continuation c.val))
    (.case (.bv 0) (continuation (composeTerm a.val c.val))
      (continuation (composeTerm b.val c.val))) D
  rw [continuation_compose, continuation_compose]
  exact .letCase cap (inputSplit _).symm (inputSplit _)
    (identityDeriv _ ⊤)
    (da.rename _ ((QCtx.Weakening.insertZero QCtx.nil _).up A))
    (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil _).up B))
    (dc.rename _ ((QCtx.Weakening.insertZero QCtx.nil _).up C))

@[simp] theorem inl_desc (hR : R.RenamingClosed) (cap : F.HasCase)
    (a : Hom (ε := ε) F R A C) (b : Hom (ε := ε) F R B C) :
    compose hR (inl cap A B) (desc hR cap a b) = a := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b => exact Quotient.sound (inl_desc_equates cap a b)

@[simp] theorem inr_desc (hR : R.RenamingClosed) (cap : F.HasCase)
    (a : Hom (ε := ε) F R A C) (b : Hom (ε := ε) F R B C) :
    compose hR (inr cap A B) (desc hR cap a b) = b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b => exact Quotient.sound (inr_desc_equates cap a b)

theorem desc_compose (hR : R.RenamingClosed) (cap : F.HasCase)
    (a : Hom (ε := ε) F R A C) (b : Hom (ε := ε) F R B C)
    (c : Hom (ε := ε) F R C D) :
    compose hR (desc hR cap a b) c = desc hR cap (compose hR a c) (compose hR b c) := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ a b c => exact Quotient.sound (desc_compose_equates cap a b c)

@[simp] theorem desc_inl_inr (hR : R.RenamingClosed) (cap : F.HasCase) (A B : τ) :
    desc (ε := ε) (R := R) hR cap (inl cap A B) (inr cap A B) = identity (coprod A B) :=
  Quotient.sound (Equates.ofAxiom (.caseEta cap (identityDeriv _ ⊤))
    (descArrow cap (inlArrow cap A B) (inrArrow cap A B)).property (identityArrow _).property)

theorem desc_unique (hR : R.RenamingClosed) (cap : F.HasCase)
    (a : Hom (ε := ε) F R A C) (b : Hom (ε := ε) F R B C)
    (c : Hom (ε := ε) F R (coprod A B) C)
    (hl : compose hR (inl cap A B) c = a) (hr : compose hR (inr cap A B) c = b) :
    c = desc hR cap a b := by
  rw [← hl, ← hr, ← desc_compose, desc_inl_inr, identity_compose]


/-- Empty inputs can be shared; this uses their declared unrestricted quantity. -/
theorem emptyInput_split :
    (input (Silmaril.empty : τ)).Split (input Silmaril.empty) (input Silmaril.empty) :=
  QCtx.Split.nil.snoc (.both (.used ⊤) (by
    simp only [Usage.effective, Usage.used_mul_used, TypeQuantity.empty_quantity, inf_top_eq,
      Usage.used_le_used]
    exact le_top))

/-- Adding a discarded unit binder is resource-valid. -/
def unitLiftDeriv {e : ε} {a : Term Φ 1} (da : HasType F (input A) e a B) :
    HasType F ((input A).snoc Silmaril.unit) e a.lift B :=
  da.rename _ (.skip (.refl _) (by
    simp only [Usage.effective, Usage.used_mul_used, TypeQuantity.unit_quantity, inf_top_eq,
      Usage.zero_le_used]
    exact le_top))

def abortThenArrow (cap : F.HasCase)
    (a : Arrow (Φ := Φ) (ε := ε) F Silmaril.empty A) :
    Arrow (Φ := Φ) (ε := ε) F Silmaril.empty A :=
  ⟨.let₁ (.abort (.bv 0)) a.val.lift, by
    obtain ⟨da⟩ := a.property
    exact ⟨.let₁ emptyInput_split (abortDeriv cap Silmaril.unit ⊤) (unitLiftDeriv da)⟩⟩

/-- A pure abort of an empty value may be discarded because the input is unrestricted. -/
theorem abortThen_equates (cap : F.HasCase)
    (a : Arrow (Φ := Φ) (ε := ε) F Silmaril.empty A) :
    Equates (ε := ε) F R (input Silmaril.empty) (abortThenArrow cap a).val a.val A := by
  obtain ⟨da⟩ := a.property
  have law (p : Polarity) : DirectionalAxiom (ε := ε) F p (input Silmaril.empty)
      (.let₁ (.abort (.bv 0)) a.val.lift) a.val A := by
    simpa only [Tm.lift, Tm.instantiate, Tm.bsubst_rename, Fin.cases_succ, Tm.bsubst_id] using
      (DirectionalAxiom.beta (p := p) emptyInput_split (abortDeriv cap Silmaril.unit ⊥)
        (da.rename Fin.succ (.skip (.refl _) le_rfl)) (unitLiftDeriv da)
        (EffectSystem.pure_moves p ⊤)
        (show Usage.zero ≤ Usage.used ((input (Silmaril.empty : τ)).linearity ⊓
            EffectSystem.quantity p (⊥ : ε)) by
          simp only [input_linearity, TypeQuantity.empty_quantity, EffectSystem.quantity_pure,
            inf_top_eq, Usage.zero_le_used]
          exact le_top))
  exact ⟨.directional .positive (law _) (abortThenArrow cap a).property a.property,
    .directional .negative (law _) (abortThenArrow cap a).property a.property⟩

/-- Initiality is derived using the written initial and pure beta rules. -/
theorem abort_unique_equates (cap : F.HasCase)
    (a : Arrow (Φ := Φ) (ε := ε) F Silmaril.empty A) :
    Equates (ε := ε) F R (input Silmaril.empty) a.val (abortArrow (ε := ε) cap A).val A := by
  obtain ⟨da⟩ := a.property
  apply (abortThen_equates (R := R) cap a).symm.trans
  apply Equates.trans (b := (abortThenArrow cap (abortArrow (ε := ε) cap A)).val)
  · exact Equates.ofAxiom
      (.initial cap emptyInput_split (identityDeriv Silmaril.empty ⊤)
        (unitLiftDeriv da) (unitLiftDeriv (abortDeriv cap A ⊤)))
      (abortThenArrow cap a).property (abortThenArrow cap (abortArrow (ε := ε) cap A)).property
  · exact abortThen_equates cap (abortArrow (ε := ε) cap A)

theorem abort_unique (cap : F.HasCase) (a : Hom (ε := ε) F R Silmaril.empty A) :
    a = abort cap A := by
  induction a using Quotient.inductionOn with
  | _ a => exact Quotient.sound (abort_unique_equates cap a)

/-- The selected signature coproducts have their actual categorical universal properties. -/
def chosenCoproducts (hR : R.RenamingClosed) (cap : F.HasCase) :
    letI := category (ε := ε) F R hR
    ChosenCoproducts τ := by
  letI := category (ε := ε) F R hR
  exact {
    sum := coprod
    zero := Silmaril.empty
    inl := inl cap
    inr := inr cap
    isColimit := fun A B => CategoryTheory.Limits.BinaryCofan.isColimitMk
      (fun s => desc hR cap s.inl s.inr)
      (fun s => inl_desc hR cap s.inl s.inr)
      (fun s => inr_desc hR cap s.inl s.inr)
      (fun s m hl hr => desc_unique hR cap s.inl s.inr m hl hr)
    isInitial := CategoryTheory.Limits.IsInitial.ofUniqueHom (abort cap)
      (fun _ a => abort_unique cap a) }


@[simp] theorem chosenCoproducts_desc (hR : R.RenamingClosed) (cap : F.HasCase)
    (a : Hom (ε := ε) F R A C) (b : Hom (ε := ε) F R B C) :
    letI := category (ε := ε) F R hR
    (chosenCoproducts hR cap).desc a b = desc hR cap a b := rfl

@[simp] theorem chosenCoproducts_abort (hR : R.RenamingClosed) (cap : F.HasCase) (A : τ) :
    letI := category (ε := ε) F R hR
    (chosenCoproducts hR cap).abort A = abort cap A := rfl

end Silmaril.Isotope.Refinement.Models.Syntactic
