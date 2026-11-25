module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.StructuralActs

/-! # Native action and sequential binding -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Right identity for action uses only a linear pure continuation. -/
theorem action_identity {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A : τ}
    (ha : HasType F Γ (⊤ : ε) a A) :
    Equates (ε := ε) F R Γ (action a (.bv 0)) a A := by
  exact linearBetaTyped (R := R) (QCtx.Split.zero_right Γ) ha
    (zeroParameter Γ A (.used .linear) (⊥ : ε) le_rfl)
    (zeroParameter Γ A (.used ⊤) (⊥ : ε) (by
      change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
      exact inf_le_inf bot_le le_rfl)) (EffectSystem.pure_commutes ⊤).symm

/-- An instruction acting on a computation is its native `op` constructor;
let reassociation supplies this law without an effect-commutation assumption. -/
theorem action_instruction {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} (f : Φ)
    (ha : HasType F Γ (⊤ : ε) a (instrSrc f)) :
    Equates (ε := ε) F R Γ (action a (.op f (.bv 0))) (.op f a) (instrTrg f) := by
  have dop := HasType.op (f := f) (show instrEff f ≤ (⊤ : ε) from le_top) ha
  have dc := atZeroDeriv Γ (identityDeriv (F := F) (Φ := Φ) (instrTrg f) (⊤ : ε))
  have db := atZeroDeriv Γ ((instructionDeriv (F := F) (ε := ε) f).top)
  have hid := action_identity (R := R) dop
  have hbody := action_identity (R := R) db
  have ht := Equates.let₁ (QCtx.Split.zero_left Γ) (Equates.refl ⟨ha⟩) hbody
  have law := Equates.ofAxiom (R := R) (.letOp (QCtx.Split.zero_left Γ) le_top ha dc)
    hid.1.wellTyped.1 ht.1.wellTyped.1
  exact ht.symm.trans (law.symm.trans hid)

/-- Acting on a let-computation acts on its continuation. -/
theorem action_let₁ {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {b : Term Φ (n + 1)} {f : Term Φ 1} {A B C : τ}
    (s : Γ.Split Γl Γr) (ha : HasType F Γr (⊤ : ε) a A)
    (hb : HasType F (Γl.snoc A) (⊤ : ε) b B)
    (hf : HasType F (input B) (⊤ : ε) f C) :
    Equates (ε := ε) F R Γ (action (.let₁ a b) f) (.let₁ a (action b f)) C := by
  have h := Equates.ofAxiom (R := R)
    (.letLet s (QCtx.Split.zero_left Γl) ha hb (atZeroDeriv Γl hf))
    ⟨actionDeriv (.let₁ s ha hb) hf⟩
    (by simpa only [action, underBinder_atIndex_zero] using
      (show WellTyped (ε := ε) F Γ (.let₁ a (action b f)) C from ⟨.let₁ s ha (actionDeriv hb hf)⟩))
  simpa only [action, underBinder_atIndex_zero] using h

/-- The continuation's packed input is precisely the retained old context
paired with the freshly computed value. -/
theorem Acts.bind_pack {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {b : Term Φ (n + 1)} {A B : τ}
    (s : Γ.Split Γl Γr) (ha : HasType F Γr (⊤ : ε) a A)
    {f : Hom (ε := ε) F R (product (packed Γl) A) B}
    (h : Acts (Γl.snoc A) (packTerm (Γl.snoc A)) f b) :
    Acts Γ (.pair (packTerm Γl) a) f (.let₁ a b) := by
  obtain ⟨r, hr, he⟩ := h
  obtain ⟨dr⟩ := r.property
  have dp := packDeriv (F := F) (Φ := Φ) Γl (⊥ : ε)
  have hpair := pair_right_bind (R := R) s dp ha
  have hpb := pairRightBindDeriv dp A (.used ⊤) (by
    change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
    exact inf_le_inf bot_le le_rfl)
  refine ⟨r, hr, ?_⟩
  exact (action_congr hpair dr).trans
    ((action_let₁ s ha hpb.top dr).trans (Equates.let₁ s (Equates.refl ⟨ha⟩) he))

end Silmaril.Isotope.Refinement.Models.Syntactic
