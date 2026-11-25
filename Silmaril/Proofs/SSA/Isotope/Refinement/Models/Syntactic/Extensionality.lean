module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Action

/-! # Product-component tests for structural arrow equations -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Test a product-valued left argument by its components, while retaining a pure right value. -/
theorem action_pair_ext_left {n : Nat} {Γ Γa Γc : QCtx τ n}
    {a c : Term Φ n} {f g : Term Φ 1} {A B C D : τ}
    (split : Γ.Split Γa Γc) (ha : HasType F Γa (⊤ : ε) a (product A B))
    (hc : HasType F Γc (⊥ : ε) c C)
    (hf : HasType F (input (product (product A B) C)) (⊤ : ε) f D)
    (hg : HasType F (input (product (product A B) C)) (⊤ : ε) g D)
    (h : Equates (ε := ε) F R ((Γc.snoc A).snoc B)
      (action (.pair (.pair (.bv 1) (.bv 0)) c.lift.lift) f)
      (action (.pair (.pair (.bv 1) (.bv 0)) c.lift.lift) g) D) :
    Equates (ε := ε) F R Γ (action (.pair a c) f) (action (.pair a c) g) D := by
  have heta := Equates.ofAxiom (R := R) (.pairEta ha)
    ⟨.let₂ (QCtx.Split.zero_left Γa) ha (pairVariables Γa A B (⊤ : ε))⟩ ⟨ha⟩
  have hpair := Equates.pair split heta.symm (Equates.refl ⟨hc.top⟩)
  have hmove := pair_let₂_left (R := R) split.symm (QCtx.Split.zero_right Γc)
    ha (pairVariables Γc A B (⊤ : ε)) hc
  have db : HasType F ((Γc.snoc A).snoc B) (⊤ : ε)
      (.pair (.pair (.bv 1) (.bv 0)) c.lift.lift) (product (product A B) C) :=
    .pair (((QCtx.Split.zero_left Γc).snoc (.left (.used ⊤))).snoc (.left (.used ⊤)))
      (pairVariables Γc A B (⊤ : ε))
      ((hc.top.rename Fin.succ (.insertZero Γc A)).rename Fin.succ (.insertZero _ B))
  have hnormalize (k : Term Φ 1)
      (hk : HasType F (input (product (product A B) C)) (⊤ : ε) k D) :
      Equates (ε := ε) F R Γ (action (.pair a c) k)
        (.let₂ a (action (.pair (.pair (.bv 1) (.bv 0)) c.lift.lift) k)) D :=
    (action_congr hpair hk).trans ((action_congr hmove hk).trans
      (action_let₂ split.symm ha db hk))
  exact (hnormalize f hf).trans
    ((Equates.let₂ split.symm (Equates.refl ⟨ha⟩) h).trans (hnormalize g hg).symm)

/-- Test a product-valued right argument by its components, while retaining a pure left value. -/
theorem action_pair_ext_right {n : Nat} {Γ Γa Γc : QCtx τ n}
    {a c : Term Φ n} {f g : Term Φ 1} {A B C D : τ}
    (split : Γ.Split Γc Γa) (ha : HasType F Γa (⊤ : ε) a (product A B))
    (hc : HasType F Γc (⊥ : ε) c C)
    (hf : HasType F (input (product C (product A B))) (⊤ : ε) f D)
    (hg : HasType F (input (product C (product A B))) (⊤ : ε) g D)
    (h : Equates (ε := ε) F R ((Γc.snoc A).snoc B)
      (action (.pair c.lift.lift (.pair (.bv 1) (.bv 0))) f)
      (action (.pair c.lift.lift (.pair (.bv 1) (.bv 0))) g) D) :
    Equates (ε := ε) F R Γ (action (.pair c a) f) (action (.pair c a) g) D := by
  have heta := Equates.ofAxiom (R := R) (.pairEta ha)
    ⟨.let₂ (QCtx.Split.zero_left Γa) ha (pairVariables Γa A B (⊤ : ε))⟩ ⟨ha⟩
  have hpair := Equates.pair split (Equates.refl ⟨hc.top⟩) heta.symm
  have hmove := pair_let₂_right (R := R) split (QCtx.Split.zero_right Γc)
    ha (pairVariables Γc A B (⊤ : ε)) hc
  have db : HasType F ((Γc.snoc A).snoc B) (⊤ : ε)
      (.pair c.lift.lift (.pair (.bv 1) (.bv 0))) (product C (product A B)) :=
    .pair (((QCtx.Split.zero_right Γc).snoc (.right (.used ⊤))).snoc (.right (.used ⊤)))
      ((hc.top.rename Fin.succ (.insertZero Γc A)).rename Fin.succ (.insertZero _ B))
      (pairVariables Γc A B (⊤ : ε))
  have hnormalize (k : Term Φ 1)
      (hk : HasType F (input (product C (product A B))) (⊤ : ε) k D) :
      Equates (ε := ε) F R Γ (action (.pair c a) k)
        (.let₂ a (action (.pair c.lift.lift (.pair (.bv 1) (.bv 0))) k)) D :=
    (action_congr hpair hk).trans ((action_congr hmove hk).trans
      (action_let₂ split ha db hk))
  exact (hnormalize f hf).trans
    ((Equates.let₂ split (Equates.refl ⟨ha⟩) h).trans (hnormalize g hg).symm)

/-- A left-nested product arrow is determined by three fresh components. -/
theorem triple_ext_left {A B C D : τ} {f g : Term Φ 1}
    (hf : HasType F (input (product (product A B) C)) (⊤ : ε) f D)
    (hg : HasType F (input (product (product A B) C)) (⊤ : ε) g D)
    (h : Equates (ε := ε) F R
      (((pairRightContext (product (product A B) C) (product A B) C).snoc A).snoc B)
      (action (.pair (.pair (.bv 1) (.bv 0)) (.bv 2)) f)
      (action (.pair (.pair (.bv 1) (.bv 0)) (.bv 2)) g) D) :
    Equates (ε := ε) F R (input (product (product A B) C)) f g D :=
  pair_ext hf hg (action_pair_ext_left (pairSplit _ _ _)
    (leftParameter _ _ _ (⊤ : ε)) (rightParameter _ _ _ (⊥ : ε)) hf hg h)

/-- The corresponding component test for a right-nested product. -/
theorem triple_ext_right {A B C D : τ} {f g : Term Φ 1}
    (hf : HasType F (input (product A (product B C))) (⊤ : ε) f D)
    (hg : HasType F (input (product A (product B C))) (⊤ : ε) g D)
    (h : Equates (ε := ε) F R
      (((pairLeftContext (product A (product B C)) A (product B C)).snoc B).snoc C)
      (action (.pair (.bv 3) (.pair (.bv 1) (.bv 0))) f)
      (action (.pair (.bv 3) (.pair (.bv 1) (.bv 0))) g) D) :
    Equates (ε := ε) F R (input (product A (product B C))) f g D :=
  pair_ext hf hg (action_pair_ext_right (pairSplit _ _ _)
    (rightParameter _ _ _ (⊤ : ε)) (leftParameter _ _ _ (⊥ : ε)) hf hg h)

end Silmaril.Isotope.Refinement.Models.Syntactic
