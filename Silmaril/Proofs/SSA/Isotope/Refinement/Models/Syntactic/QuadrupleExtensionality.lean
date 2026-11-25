module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Extensionality

/-! # Four-component extensionality for associativity coherence -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- A product component inside two retained pure pairings can be tested by its variables. -/
theorem action_double_pair_ext_left {n : Nat} {Γ Γac Γa Γc Γd Γcd : QCtx τ n}
    {a c d : Term Φ n} {f g : Term Φ 1} {A B C D E : τ}
    (s : Γ.Split Γac Γd) (t : Γac.Split Γa Γc)
    (u : Γ.Split Γcd Γa) (v : Γcd.Split Γd Γc)
    (ha : HasType F Γa (⊤ : ε) a (product A B))
    (hc : HasType F Γc (⊥ : ε) c C) (hd : HasType F Γd (⊥ : ε) d D)
    (hf : HasType F (input (product (product (product A B) C) D)) (⊤ : ε) f E)
    (hg : HasType F (input (product (product (product A B) C) D)) (⊤ : ε) g E)
    (h : Equates (ε := ε) F R ((Γcd.snoc A).snoc B)
      (action (.pair (.pair (.pair (.bv 1) (.bv 0)) c.lift.lift) d.lift.lift) f)
      (action (.pair (.pair (.pair (.bv 1) (.bv 0)) c.lift.lift) d.lift.lift) g) E) :
    Equates (ε := ε) F R Γ (action (.pair (.pair a c) d) f)
      (action (.pair (.pair a c) d) g) E := by
  have heta := Equates.ofAxiom (R := R) (.pairEta ha)
    ⟨.let₂ (QCtx.Split.zero_left Γa) ha (pairVariables Γa A B (⊤ : ε))⟩ ⟨ha⟩
  have h₀ := Equates.pair s (Equates.pair t heta.symm (Equates.refl ⟨hc.top⟩))
    (Equates.refl ⟨hd.top⟩)
  have h₁ := Equates.pair s
    (pair_let₂_left (R := R) t.symm (QCtx.Split.zero_right Γc) ha
      (pairVariables Γc A B (⊤ : ε)) hc) (Equates.refl ⟨hd.top⟩)
  have db : HasType F ((Γc.snoc A).snoc B) (⊤ : ε)
      (.pair (.pair (.bv 1) (.bv 0)) c.lift.lift) (product (product A B) C) :=
    .pair (((QCtx.Split.zero_left Γc).snoc (.left (.used ⊤))).snoc (.left (.used ⊤)))
      (pairVariables Γc A B (⊤ : ε))
      ((hc.top.rename Fin.succ (.insertZero Γc A)).rename Fin.succ (.insertZero _ B))
  have h₂ := pair_let₂_left (R := R) u v ha db hd
  have de : HasType F ((Γcd.snoc A).snoc B) (⊤ : ε)
      (.pair (.pair (.pair (.bv 1) (.bv 0)) c.lift.lift) d.lift.lift)
      (product (product (product A B) C) D) :=
    .pair ((v.symm.snoc (.left (.used ⊤))).snoc (.left (.used ⊤))) db
      ((hd.top.rename Fin.succ (.insertZero Γd A)).rename Fin.succ (.insertZero _ B))
  have hn (k : Term Φ 1)
      (hk : HasType F (input (product (product (product A B) C) D)) (⊤ : ε) k E) :
      Equates (ε := ε) F R Γ (action (.pair (.pair a c) d) k)
        (.let₂ a (action (.pair (.pair (.pair (.bv 1) (.bv 0)) c.lift.lift) d.lift.lift) k)) E :=
    (action_congr h₀ hk).trans ((action_congr h₁ hk).trans
      ((action_congr h₂ hk).trans (action_let₂ u ha de hk)))
  exact (hn f hf).trans ((Equates.let₂ u (Equates.refl ⟨ha⟩) h).trans (hn g hg).symm)

/-- Four fresh variables suffice to compare arrows from a left-associated fourfold product. -/
theorem quadruple_ext_left {A B C D E : τ} {f g : Term Φ 1}
    (hf : HasType F (input (product (product (product A B) C) D)) (⊤ : ε) f E)
    (hg : HasType F (input (product (product (product A B) C) D)) (⊤ : ε) g E)
    (h : Equates (ε := ε) F R
      (((((pairRightContext (product (product (product A B) C) D)
        (product (product A B) C) D).snoc (product A B) .zero).snoc C).snoc A).snoc B)
      (action (.pair (.pair (.pair (.bv 1) (.bv 0)) (.bv 2)) (.bv 4)) f)
      (action (.pair (.pair (.pair (.bv 1) (.bv 0)) (.bv 2)) (.bv 4)) g) E) :
    Equates (ε := ε) F R (input (product (product (product A B) C) D)) f g E := by
  apply triple_ext_left hf hg
  let P := product (product (product A B) C) D
  let Γa : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product (product A B) C) .zero).snoc D .zero).snoc (product A B)).snoc C .zero
  let Γc : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product (product A B) C) .zero).snoc D .zero).snoc (product A B) .zero).snoc C
  let Γd : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product (product A B) C) .zero).snoc D).snoc (product A B) .zero).snoc C .zero
  have da := singleVariable (F := F) (Φ := Φ) Γa 1 (⊤ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dc := singleVariable (F := F) (Φ := Φ) Γc 0 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dd := singleVariable (F := F) (Φ := Φ) Γd 2 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  exact action_double_pair_ext_left
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.right (.used ⊤))).snoc (.left (.used ⊤))).snoc (.left (.used ⊤)))
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left .zero)).snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left (.used ⊤))).snoc (.right (.used ⊤))).snoc (.left (.used ⊤)))
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left (.used ⊤))).snoc (.left .zero)).snoc (.right (.used ⊤)))
    da dc dd hf hg h

end Silmaril.Isotope.Refinement.Models.Syntactic
