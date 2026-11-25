module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterationConway

/-! # Directed, effect-sensitive native iteration uniformity -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ} {A B C D : τ}

theorem action_sumMap_right {n : Nat} {Γ : QCtx τ n} {a : Term Φ n}
    {h : Term Φ 1} (cap : F.HasCase)
    (ha : HasType F Γ (⊤ : ε) a (coprod D A))
    (hh : HasType F (input A) (⊤ : ε) h B) :
    Equates (ε := ε) F R Γ
      (action a (descTerm (.inl (.bv 0)) (composeTerm h (.inr (.bv 0)))))
      (.case a (.inl (.bv 0)) (.inr (atIndex 0 h))) (coprod D B) := by
  have hd := action_desc (R := R) cap ha (inlDeriv cap D B (⊤ : ε))
    (composeDeriv hh (inrDeriv cap D B (⊤ : ε)))
  simp only [atIndex_compose] at hd
  exact hd.trans (Equates.case cap (QCtx.Split.zero_left Γ) (Equates.refl ⟨ha⟩)
    (Equates.refl ⟨atZeroDeriv Γ (inlDeriv cap D B (⊤ : ε))⟩)
    (action_inr cap (atZeroDeriv Γ hh)))

theorem iterate_uniformity (hR : R.RenamingClosed) (cap : F.HasIter) (p : Polarity)
    {e η : ε} {h : Hom (ε := ε) F R A B} {f : Hom (ε := ε) F R B (coprod D B)}
    {g : Hom (ε := ε) F R A (coprod D A)}
    (he : EffectSystem.iterable e) (hm : EffectSystem.moves p η e)
    (hh : hasEffect η h) (hf : hasEffect e f)
    (hs : p.orient (· ≤ ·) (compose (R := R) hR h f)
      (compose (R := R) hR g (desc (R := R) hR (iter_hasCase cap) (inl (iter_hasCase cap) D B)
        (compose (R := R) hR h (inr (iter_hasCase cap) D B))))) :
    p.orient (· ≤ ·) (compose (R := R) hR h (iterate (R := R) hR cap f)) (iterate (R := R) hR cap g) := by
  obtain ⟨h, rfl, ⟨dh⟩⟩ := hh
  obtain ⟨f, rfl, ⟨df⟩⟩ := hf
  induction g using Quotient.inductionOn with
  | _ g =>
    obtain ⟨dg⟩ := g.property
    let cc := iter_hasCase cap
    let r : Arrow (Φ := Φ) (ε := ε) F A (coprod D B) :=
      ⟨.case g.val (.inl (.bv 0)) (.inr (atIndex 0 h.val)),
        ⟨.case cc (QCtx.Split.zero_left (input A)) dg
          (atZeroDeriv (input A) (inlDeriv cc D B ⊤))
          (.inr cc (atZeroDeriv (input A) dh.top))⟩⟩
    have hr : compose (R := R) hR (ofArrow g)
        (desc (R := R) hR cc (inl cc D B) (compose (R := R) hR (ofArrow h) (inr cc D B))) = ofArrow r := by
      apply Quotient.sound
      change Equates (ε := ε) F R (input A) _ r.val (coprod D B)
      simpa only [composeArrow, composeTerm, descArrow, inlArrow, inrArrow,
        continuation_atIndex, r, action] using (action_sumMap_right (R := R) cc dg dh.top)
    change p.orient (· ≤ ·) (compose (R := R) hR (ofArrow h) (ofArrow f))
      (compose (R := R) hR (ofArrow g)
        (desc (R := R) hR cc (inl cc D B)
          (compose (R := R) hR (ofArrow h) (inr cc D B)))) at hs
    rw [hr] at hs
    have hsq : Refines (ε := ε) F R (input A)
        (p.source (composeArrow h f).val r.val) (p.target (composeArrow h f).val r.val)
        (coprod D B) := by cases p <;> exact hs
    have hsq' := hsq.rename _ ((QCtx.Weakening.empty (input A).zero (input A).zero_discardable).up A) hR
    let l : Arrow (Φ := Φ) (ε := ε) F A D :=
      ⟨.iter h.val (atIndex 0 f.val),
        ⟨.iter cap (QCtx.Split.zero_left (input A)) (input A).zero_linearity
          EffectSystem.iterable_top dh.top (atZeroDeriv (input A) df.top)⟩⟩
    have hl : compose (R := R) hR (ofArrow h) (iterate (R := R) hR cap (ofArrow f)) = ofArrow l := by
      apply Quotient.sound
      change Equates (ε := ε) F R (input A) _ l.val D
      simpa only [composeArrow, composeTerm, iterateArrow, continuation_atIndex, l, action] using
        (action_iterate (R := R) cap dh.top df.top)
    have law := UniformityRule.square (ε := ε) (p := p) cap
      (QCtx.Split.zero_left (input A)) (QCtx.Split.zero_left (input A).zero)
      (input A).zero.zero_linearity he (identityDeriv A e)
      (atZeroDeriv (input A) dh) (atZeroDeriv (input A).zero df)
      (atZeroDeriv (input A).zero dg) (atZeroDeriv (input A) (identityDeriv D (⊤ : ε))) hm
    have hnative : Refines (ε := ε) F R (input A)
        (p.source (composeArrow (identityArrow A) l).val
          (composeArrow (iterateArrow cap g) (identityArrow D)).val)
        (p.target (composeArrow (identityArrow A) l).val
          (composeArrow (iterateArrow cap g) (identityArrow D)).val) D := by
      have hsq'' : Refines (ε := ε) F R ((input A).zero.snoc A)
          (p.source (.let₁ (atIndex 0 h.val) (atIndex 0 f.val))
            (.case (atIndex 0 g.val) (.inl (.bv 0)) (.inr (atIndex 0 h.val))))
          (p.target (.let₁ (atIndex 0 h.val) (atIndex 0 f.val))
            (.case (atIndex 0 g.val) (.inl (.bv 0)) (.inr (atIndex 0 h.val)))) (coprod D B) := by
        have hρ : Tm.up (Fin.elim0 : Fin 0 → Fin 1) = fun _ : Fin 1 => (0 : Fin 2) := by
          funext i
          have hi : i = 0 := Fin.eq_zero i
          subst i
          rfl
        rw [hρ] at hsq'
        cases p <;>
          simpa only [composeArrow, composeTerm, continuation_atIndex, r, atIndex,
            Tm.rename, Tm.rename_comp, Tm.up, Fin.cases_zero, Polarity.source,
            Polarity.target, Polarity.orient] using hsq'
      have hleft : WellTyped (ε := ε) F (input A)
          (.let₁ (.bv 0) (.iter (atIndex 0 h.val) (atIndex 0 f.val))) D := by
        simpa only [composeArrow, composeTerm, identityArrow, l, continuation_atIndex,
          atIndex, Tm.rename, Tm.rename_comp, Tm.up, Fin.cases_zero] using
          (composeArrow (identityArrow A) l).property
      have hn := Refines.uniformity (R := R) p law
        (by simpa only [underBinder_atIndex_zero] using hleft)
        (by simpa only [composeArrow, composeTerm, iterateArrow, iterateTerm, identityArrow,
          continuation_atIndex] using (composeArrow (iterateArrow cap g) (identityArrow D)).property)
        (by simpa only [underBinder_atIndex_zero, atIndex, Tm.rename, Tm.underBinder,
          Tm.rename_comp, Tm.up, Fin.cases_zero] using hsq'')
      simpa only [composeArrow, composeTerm, identityArrow, iterateArrow, iterateTerm, l,
        continuation_atIndex, underBinder_atIndex_zero, atIndex, Tm.rename, Tm.underBinder,
        Tm.rename_comp, Tm.up, Fin.cases_zero] using hn
    have hfinal : p.orient (· ≤ ·)
        (compose (R := R) hR (identity A) (ofArrow l))
        (compose (R := R) hR (iterate (R := R) hR cap (ofArrow g)) (identity D)) := by cases p <;> exact hnative
    rw [identity_compose, compose_identity, ← hl] at hfinal
    exact hfinal

end Silmaril.Isotope.Refinement.Models.Syntactic
