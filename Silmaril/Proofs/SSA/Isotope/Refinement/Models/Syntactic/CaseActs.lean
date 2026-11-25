module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.ProductBindingActs
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterationStrength
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Operations

/-! # Native action of branching interpretation

Injection, elimination, and the distributivity isomorphism act by the written
case rules. These facts retain the ambient quantitative context explicitly.
-/

@[expose] public section
noncomputable section
universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless Denotation CategoryTheory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

@[simp] theorem caseData_distribute (hR : R.RenamingClosed) (cap : F.HasCase) (D A B : τ) :
    (caseData (ε := ε) (R := R) hR cap).distribute D A B =
      distributorInv (R := R) cap D A B := by
  let := category (ε := ε) F R hR
  let := typePremonoidal (ε := ε) (F := F) (R := R) hR
  let := typeSymmetric (ε := ε) (F := F) (R := R) hR
  let := typeHomOrder (ε := ε) (F := F) (R := R) hR
  let := (typeCaseCategory (ε := ε) (R := R) hR cap).distributor_isIso D A B
  have hi : inv ((chosenCoproducts (ε := ε) (R := R) hR cap).distributor D A B) =
      distributorInv (R := R) cap D A B :=
    IsIso.inv_eq_of_hom_inv_id (distributor_distributorInv hR cap D A B)
  change compose (R := R) hR (identity _) (compose (R := R) hR
    (inv ((chosenCoproducts (ε := ε) (R := R) hR cap).distributor D A B)) (identity _)) = _
  rw [hi, identity_compose]
  exact compose_identity (ε := ε) (F := F) (R := R) hR (distributorInv cap D A B)

theorem action_abort {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A : τ}
    (cap : F.HasCase) (ha : HasType F Γ (⊤ : ε) a Silmaril.empty) :
    Equates (ε := ε) F R Γ (action a (.abort (.bv 0))) (.abort a) A := by
  exact linearBeta (QCtx.Split.zero_right Γ) ha
    (.abort cap (zeroParameter Γ Silmaril.empty (.used .linear) (⊥ : ε) le_rfl))
    (atZeroDeriv Γ (abortDeriv cap A (⊥ : ε)))
    (EffectSystem.pure_commutes (⊤ : ε)).symm ⟨.abort cap ha⟩

theorem Acts.inl {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A B : τ}
    (cap : F.HasCase) (ha : HasType F Γ (⊤ : ε) a A) :
    Acts Γ a (Syntactic.inl (ε := ε) (R := R) cap A B) (.inl a) :=
  .of_equates (r := inlArrow cap A B) (action_inl cap ha)

theorem Acts.inr {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A B : τ}
    (cap : F.HasCase) (ha : HasType F Γ (⊤ : ε) a B) :
    Acts Γ a (Syntactic.inr (ε := ε) (R := R) cap A B) (.inr a) :=
  .of_equates (r := inrArrow cap A B) (action_inr cap ha)

theorem Acts.abort {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A : τ}
    (cap : F.HasCase) (ha : HasType F Γ (⊤ : ε) a Silmaril.empty) :
    Acts Γ a (Syntactic.abort (ε := ε) (R := R) cap A) (.abort a) :=
  .of_equates (r := abortArrow cap A) (action_abort cap ha)

theorem Acts.desc_inl (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n}
    {a b : Term Φ n} {A B C : τ} (cap : F.HasCase)
    (ha : HasType F Γ (⊤ : ε) a A)
    {f : Hom (ε := ε) F R A C} (g : Hom (ε := ε) F R B C)
    (h : Acts Γ a f b) : Acts Γ (.inl a) (desc hR cap f g) b := by
  obtain ⟨r, rfl, he⟩ := h
  induction g using Quotient.inductionOn with
  | _ s =>
    obtain ⟨dr⟩ := r.property
    obtain ⟨ds⟩ := s.property
    refine ⟨descArrow cap r s, rfl, ?_⟩
    apply (action_desc cap (.inl cap ha) dr ds).trans
    exact (Equates.ofAxiom (.caseBetaL cap (QCtx.Split.zero_left Γ) ha
      (atZeroDeriv Γ dr) (atZeroDeriv Γ ds))
      ⟨.case cap (QCtx.Split.zero_left Γ) (.inl cap ha)
        (atZeroDeriv Γ dr) (atZeroDeriv Γ ds)⟩ ⟨actionDeriv ha dr⟩).trans he

theorem Acts.desc_inr (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n}
    {a b : Term Φ n} {A B C : τ} (cap : F.HasCase)
    (ha : HasType F Γ (⊤ : ε) a B)
    (f : Hom (ε := ε) F R A C) {g : Hom (ε := ε) F R B C}
    (h : Acts Γ a g b) : Acts Γ (.inr a) (desc hR cap f g) b := by
  obtain ⟨s, rfl, he⟩ := h
  induction f using Quotient.inductionOn with
  | _ r =>
    obtain ⟨dr⟩ := r.property
    obtain ⟨ds⟩ := s.property
    refine ⟨descArrow cap r s, rfl, ?_⟩
    apply (action_desc cap (.inr cap ha) dr ds).trans
    exact (Equates.ofAxiom (.caseBetaR cap (QCtx.Split.zero_left Γ) ha
      (atZeroDeriv Γ dr) (atZeroDeriv Γ ds))
      ⟨.case cap (QCtx.Split.zero_left Γ) (.inr cap ha)
        (atZeroDeriv Γ dr) (atZeroDeriv Γ ds)⟩ ⟨actionDeriv ha ds⟩).trans he

theorem Acts.case (hR : R.RenamingClosed) {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {l l' r r' : Term Φ (n + 1)} {A B C D : τ}
    (cap : F.HasCase) (s : Γ.Split Γl Γr) (ha : HasType F Γr (⊤ : ε) a (coprod A B))
    (hl : HasType F (Γl.snoc A) (⊤ : ε) l C)
    (hr : HasType F (Γl.snoc B) (⊤ : ε) r C)
    {f : Hom (ε := ε) F R C D}
    (h : Acts (Γl.snoc A) l f l') (k : Acts (Γl.snoc B) r f r') :
    Acts Γ (.case a l r) f (.case a l' r') := by
  obtain ⟨rep, hrep, he⟩ := h
  obtain ⟨drep⟩ := rep.property
  have ke := k.representative hR hr rep hrep
  exact ⟨rep, hrep, (action_case cap s ha hl hr drep).trans
    (Equates.case cap s (Equates.refl ⟨ha⟩) he ke)⟩

/-- Distribute the retained packing into the selected branch, then execute the
branch interpretation. -/
theorem Acts.bindCase_pack (hR : R.RenamingClosed) {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {l r : Term Φ (n + 1)} {A B C : τ}
    (cap : F.HasCase) (s : Γ.Split Γl Γr) (hΓl : Γl.DefaultAnnotations)
    (ha : HasType F Γr (⊤ : ε) a (coprod A B))
    {f : Hom (ε := ε) F R (product (packed Γl) A) C}
    {g : Hom (ε := ε) F R (product (packed Γl) B) C}
    (h : Acts (Γl.snoc A) (packTerm (Γl.snoc A)) f l)
    (k : Acts (Γl.snoc B) (packTerm (Γl.snoc B)) g r) :
    Acts Γ (.pair (packTerm Γl) a)
      (Syntactic.compose hR (distributorInv cap (packed Γl) A B) (desc hR cap f g))
      (.case a l r) := by
  have dp := packDeriv (F := F) (Φ := Φ) Γl (⊥ : ε)
  have h₀ := Acts.of_equates (r := distributorInvArrow cap (packed Γl) A B)
    (distributorInv_action (R := R) cap s dp ha (packed_quantity_eq hΓl).le)
  have h₁ := (h.desc_inl hR cap (packDeriv _ (⊤ : ε)) g).case hR cap s ha
    (.inl cap (packDeriv _ (⊤ : ε))) (.inr cap (packDeriv _ (⊤ : ε)))
    (k.desc_inr hR cap (packDeriv _ (⊤ : ε)) f)
  exact h₀.compose hR (HasType.pair s dp.top ha) h₁

end Silmaril.Isotope.Refinement.Models.Syntactic
