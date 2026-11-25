module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Category

/-! # Native operations on the syntactic quotient

Every operation descends by native congruence and resource-valid renaming. Its
order monotonicity and effect membership follow from those same derivations.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ} {A B C : τ}

theorem left_refines (hR : R.RenamingClosed) (A : τ)
    {a b : Arrow (Φ := Φ) (ε := ε) F B C}
    (h : Refines (ε := ε) F R (input B) a.val b.val C) :
    Refines (ε := ε) F R (input (product A B)) (leftArrow A a).val (leftArrow A b).val
      (product A C) := by
  apply Refines.let₂ (inputSplit _) (.refl ⟨identityDeriv _ _⟩)
  apply Refines.pair (pairSplit _ _ _) (.refl ⟨leftParameter _ _ _ _⟩)
  exact h.rename _ (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl) hR

theorem right_refines (hR : R.RenamingClosed) (C : τ)
    {a b : Arrow (Φ := Φ) (ε := ε) F A B}
    (h : Refines (ε := ε) F R (input A) a.val b.val B) :
    Refines (ε := ε) F R (input (product A C)) (rightArrow a C).val (rightArrow b C).val
      (product B C) := by
  apply Refines.let₂ (inputSplit _) (.refl ⟨identityDeriv _ _⟩)
  apply Refines.pair (pairSplit _ _ _) _ (.refl ⟨rightParameter _ _ _ _⟩)
  exact h.rename _ (.skip (.cons (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl) hR

def left (hR : R.RenamingClosed) (A : τ) (a : Hom (ε := ε) F R B C) :
    Hom (ε := ε) F R (product A B) (product A C) :=
  Quotient.map (sa := arrowSetoid (ε := ε) F R B C) (leftArrow A) (fun _ _ h =>
    ⟨left_refines hR A h.1, left_refines hR A h.2⟩) a

def right (hR : R.RenamingClosed) (a : Hom (ε := ε) F R A B) (C : τ) :
    Hom (ε := ε) F R (product A C) (product B C) :=
  Quotient.map (sa := arrowSetoid (ε := ε) F R A B) (fun a => rightArrow a C) (fun _ _ h =>
    ⟨right_refines hR C h.1, right_refines hR C h.2⟩) a

@[simp] theorem left_ofArrow (hR : R.RenamingClosed) (A : τ)
    (a : Arrow (Φ := Φ) (ε := ε) F B C) :
    left (R := R) hR A (ofArrow a) = ofArrow (leftArrow A a) := rfl

@[simp] theorem right_ofArrow (hR : R.RenamingClosed) (C : τ)
    (a : Arrow (Φ := Φ) (ε := ε) F A B) :
    right (R := R) hR (ofArrow a) C = ofArrow (rightArrow a C) := rfl

theorem left_mono (hR : R.RenamingClosed) (A : τ)
    {a b : Hom (ε := ε) F R B C} (h : a ≤ b) : left hR A a ≤ left hR A b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b => exact left_refines hR A h

theorem right_mono (hR : R.RenamingClosed) (C : τ)
    {a b : Hom (ε := ε) F R A B} (h : a ≤ b) : right hR a C ≤ right hR b C := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b => exact right_refines hR C h

theorem left_effect (hR : R.RenamingClosed) (A : τ)
    {e : ε} {a : Hom (ε := ε) F R B C} (h : hasEffect e a) : hasEffect e (left hR A a) := by
  obtain ⟨a, rfl, ⟨da⟩⟩ := h
  exact ⟨leftArrow A a, rfl, ⟨leftDeriv A da⟩⟩

theorem right_effect (hR : R.RenamingClosed) (C : τ)
    {e : ε} {a : Hom (ε := ε) F R A B} (h : hasEffect e a) : hasEffect e (right hR a C) := by
  obtain ⟨a, rfl, ⟨da⟩⟩ := h
  exact ⟨rightArrow a C, rfl, ⟨rightDeriv C da⟩⟩

def instruction (f : Φ) : Hom (ε := ε) F R (instrSrc f : τ) (instrTrg f : τ) :=
  ofArrow (instructionArrow f)

theorem instruction_effect (f : Φ) :
    hasEffect (instrEff f : ε) (instruction (F := F) (R := R) f) :=
  ⟨instructionArrow f, rfl, ⟨instructionDeriv f⟩⟩

def discard (A : τ) (hA : Quantity.affine ≤ quantity A) :
    Hom (ε := ε) F R A Silmaril.unit := ofArrow (discardArrow A hA)

def copy (A : τ) (hA : Quantity.relevant ≤ quantity A) :
    Hom (ε := ε) F R A (product A A) := ofArrow (copyArrow A hA)

theorem discard_pure (A : τ) (hA : Quantity.affine ≤ quantity A) :
    hasEffect (⊥ : ε) (discard (F := F) (R := R) A hA) :=
  ⟨discardArrow A hA, rfl, ⟨discardDeriv A hA ⊥⟩⟩

theorem copy_pure (A : τ) (hA : Quantity.relevant ≤ quantity A) :
    hasEffect (⊥ : ε) (copy (F := F) (R := R) A hA) :=
  ⟨copyArrow A hA, rfl, ⟨copyDeriv A hA ⊥⟩⟩

def inl (cap : F.HasCase) (A B : τ) : Hom (ε := ε) F R A (coprod A B) :=
  ofArrow (inlArrow cap A B)

def inr (cap : F.HasCase) (A B : τ) : Hom (ε := ε) F R B (coprod A B) :=
  ofArrow (inrArrow cap A B)

def abort (cap : F.HasCase) (A : τ) : Hom (ε := ε) F R Silmaril.empty A :=
  ofArrow (abortArrow cap A)

theorem inl_pure (cap : F.HasCase) (A B : τ) :
    hasEffect (⊥ : ε) (inl (R := R) cap A B) :=
  ⟨inlArrow cap A B, rfl, ⟨inlDeriv cap A B ⊥⟩⟩

theorem inr_pure (cap : F.HasCase) (A B : τ) :
    hasEffect (⊥ : ε) (inr (R := R) cap A B) :=
  ⟨inrArrow cap A B, rfl, ⟨inrDeriv cap A B ⊥⟩⟩

theorem abort_pure (cap : F.HasCase) (A : τ) :
    hasEffect (⊥ : ε) (abort (R := R) cap A) :=
  ⟨abortArrow cap A, rfl, ⟨abortDeriv cap A ⊥⟩⟩

theorem desc_refines (hR : R.RenamingClosed) (cap : F.HasCase)
    {a a' : Arrow (Φ := Φ) (ε := ε) F A C} {b b' : Arrow (Φ := Φ) (ε := ε) F B C}
    (ha : Refines (ε := ε) F R (input A) a.val a'.val C)
    (hb : Refines (ε := ε) F R (input B) b.val b'.val C) :
    Refines (ε := ε) F R (input (coprod A B)) (descArrow cap a b).val
      (descArrow cap a' b').val C :=
  .case cap (inputSplit _) (.refl ⟨identityDeriv _ _⟩)
    (ha.rename _ ((QCtx.Weakening.insertZero QCtx.nil _).up A) hR)
    (hb.rename _ ((QCtx.Weakening.insertZero QCtx.nil _).up B) hR)

def desc (hR : R.RenamingClosed) (cap : F.HasCase)
    (a : Hom (ε := ε) F R A C) (b : Hom (ε := ε) F R B C) :
    Hom (ε := ε) F R (coprod A B) C :=
  Quotient.map₂ (sa := arrowSetoid (ε := ε) F R A C)
    (sb := arrowSetoid (ε := ε) F R B C) (descArrow cap) (fun _ _ ha _ _ hb =>
    ⟨desc_refines hR cap ha.1 hb.1, desc_refines hR cap ha.2 hb.2⟩) a b

@[simp] theorem desc_ofArrow (hR : R.RenamingClosed) (cap : F.HasCase)
    (a : Arrow (Φ := Φ) (ε := ε) F A C) (b : Arrow (Φ := Φ) (ε := ε) F B C) :
    desc (R := R) hR cap (ofArrow a) (ofArrow b) = ofArrow (descArrow cap a b) := rfl

theorem desc_mono (hR : R.RenamingClosed) (cap : F.HasCase)
    {a a' : Hom (ε := ε) F R A C} {b b' : Hom (ε := ε) F R B C}
    (ha : a ≤ a') (hb : b ≤ b') : desc hR cap a b ≤ desc hR cap a' b' := by
  induction a, a' using Quotient.inductionOn₂ with
  | _ a a' =>
    induction b, b' using Quotient.inductionOn₂ with
    | _ b b' => exact desc_refines hR cap ha hb

theorem desc_effect (hR : R.RenamingClosed) (cap : F.HasCase) {e : ε}
    {a : Hom (ε := ε) F R A C} {b : Hom (ε := ε) F R B C}
    (ha : hasEffect e a) (hb : hasEffect e b) : hasEffect e (desc hR cap a b) := by
  obtain ⟨a, rfl, ⟨da⟩⟩ := ha
  obtain ⟨b, rfl, ⟨db⟩⟩ := hb
  exact ⟨descArrow cap a b, rfl, ⟨descDeriv cap da db⟩⟩

theorem iterate_refines (hR : R.RenamingClosed) (cap : F.HasIter)
    {a b : Arrow (Φ := Φ) (ε := ε) F A (coprod B A)}
    (h : Refines (ε := ε) F R (input A) a.val b.val (coprod B A)) :
    Refines (ε := ε) F R (input A) (iterateArrow cap a).val (iterateArrow cap b).val B :=
  .iter cap (inputSplit A) (zeroInput_linearity A) (.refl ⟨identityDeriv _ _⟩)
    (h.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up A) hR)

def iterate (hR : R.RenamingClosed) (cap : F.HasIter)
    (a : Hom (ε := ε) F R A (coprod B A)) : Hom (ε := ε) F R A B :=
  Quotient.map (sa := arrowSetoid (ε := ε) F R A (coprod B A)) (iterateArrow cap) (fun _ _ h =>
    ⟨iterate_refines hR cap h.1, iterate_refines hR cap h.2⟩) a

@[simp] theorem iterate_ofArrow (hR : R.RenamingClosed) (cap : F.HasIter)
    (a : Arrow (Φ := Φ) (ε := ε) F A (coprod B A)) :
    iterate (R := R) hR cap (ofArrow a) = ofArrow (iterateArrow cap a) := rfl

theorem iterate_mono (hR : R.RenamingClosed) (cap : F.HasIter)
    {a b : Hom (ε := ε) F R A (coprod B A)} (h : a ≤ b) :
    iterate hR cap a ≤ iterate hR cap b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b => exact iterate_refines hR cap h

theorem iterate_effect (hR : R.RenamingClosed) (cap : F.HasIter) {e : ε}
    (iterable : EffectSystem.iterable e) {a : Hom (ε := ε) F R A (coprod B A)}
    (ha : hasEffect e a) : hasEffect e (iterate hR cap a) := by
  obtain ⟨a, rfl, ⟨da⟩⟩ := ha
  exact ⟨iterateArrow cap a, rfl, ⟨iterateDeriv cap iterable da⟩⟩

end Silmaril.Isotope.Refinement.Models.Syntactic
