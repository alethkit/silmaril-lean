module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterationReduction

/-! # Conway equations of the native syntactic quotient -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless CategoryTheory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ} {A B C D : τ}

theorem iterate_fixpoint_equates (cap : F.HasIter)
    (f : Arrow (Φ := Φ) (ε := ε) F A (coprod B A)) :
    Equates (ε := ε) F R (input A) (iterateArrow cap f).val
      (composeArrow f (descArrow (iter_hasCase cap) (identityArrow B) (iterateArrow cap f))).val B := by
  obtain ⟨hf⟩ := f.property
  let c : Arrow (Φ := Φ) (ε := ε) F A B :=
    ⟨.case f.val (atIndex 0 (.bv 0)) (atIndex 0 (iterateTerm f.val)),
      ⟨.case (iter_hasCase cap) (QCtx.Split.zero_left (input A)) hf
        (atZeroDeriv (input A) (identityDeriv B ⊤))
        (atZeroDeriv (input A) (iterateDeriv cap EffectSystem.iterable_top hf))⟩⟩
  have h : Equates (ε := ε) F R (input A) (iterateArrow cap f).val
      (composeArrow (identityArrow A) c).val B := by
    apply Equates.ofAxiom _ (iterateArrow cap f).property (composeArrow (identityArrow A) c).property
    have law := EquationAxiom.fixpoint (ε := ε) cap (QCtx.Split.zero_left (input A)) (input A).zero_linearity
      EffectSystem.iterable_top (identityDeriv A (⊤ : ε)) (atZeroDeriv (input A) hf)
    simpa only [iterateArrow, iterateTerm, composeArrow, composeTerm, identityArrow, c,
      continuation_atIndex, atIndex_iterateTerm, underBinder_atIndex_zero, atIndex, Tm.rename, Tm.underBinder,
      Tm.rename_comp, Tm.up, Fin.cases_zero] using law
  apply h.trans ((identity_compose_equates R c).trans _)
  simpa only [composeArrow, composeTerm, descArrow, identityArrow, iterateArrow,
    continuation_atIndex, c, action] using
    (action_desc (R := R) (iter_hasCase cap) hf (identityDeriv B (⊤ : ε))
      (iterateDeriv cap EffectSystem.iterable_top hf)).symm

@[simp] theorem iterate_fixpoint (hR : R.RenamingClosed) (cap : F.HasIter)
    (f : Hom (ε := ε) F R A (coprod B A)) :
    iterate hR cap f = compose hR f (desc hR (iter_hasCase cap) (identity B) (iterate hR cap f)) := by
  induction f using Quotient.inductionOn with
  | _ f => exact Quotient.sound (iterate_fixpoint_equates cap f)


theorem iterate_naturality (hR : R.RenamingClosed) (cap : F.HasIter)
    (f : Hom (ε := ε) F R A (coprod B A)) (g : Hom (ε := ε) F R B C) :
    compose hR (iterate hR cap f) g = iterate hR cap
      (compose hR f (desc hR (iter_hasCase cap)
        (compose hR g (inl (iter_hasCase cap) C A)) (inr (iter_hasCase cap) C A))) := by
  induction f, g using Quotient.inductionOn₂ with
  | _ f g =>
    obtain ⟨hf⟩ := f.property
    obtain ⟨hg⟩ := g.property
    let cc := iter_hasCase cap
    let c : Arrow (Φ := Φ) (ε := ε) F A (coprod C A) :=
      ⟨.case f.val (.inl (atIndex 0 g.val)) (.inr (.bv 0)),
        ⟨.case cc (QCtx.Split.zero_left (input A)) hf
          (.inl cc (atZeroDeriv (input A) hg))
          (atZeroDeriv (input A) (inrDeriv cc C A ⊤))⟩⟩
    have hn : Equates (ε := ε) F R (input A)
        (composeArrow (iterateArrow cap f) g).val (iterateArrow cap c).val C := by
      apply Equates.ofAxiom _ (composeArrow (iterateArrow cap f) g).property
        (iterateArrow cap c).property
      have law := EquationAxiom.naturality (ε := ε) cap
        (QCtx.Split.zero_left (input A)) (QCtx.Split.zero_left (input A))
        (input A).zero_linearity (input A).zero_linearity (identityDeriv A (⊤ : ε))
        (atZeroDeriv (input A) hf) (atZeroDeriv (input A) hg)
      simpa only [iterateArrow, iterateTerm, composeArrow, composeTerm, c,
        continuation_atIndex, underBinder_atIndex_zero, atIndex, Tm.rename, Tm.underBinder,
        Tm.rename_comp, Tm.up, Fin.cases_zero] using law
    have hc : Equates (ε := ε) F R (input A)
        (composeArrow f (descArrow cc (composeArrow g (inlArrow cc C A)) (inrArrow cc C A))).val
        c.val (coprod C A) := by
      have hd := action_desc (R := R) cc hf (composeDeriv hg (inlDeriv cc C A (⊤ : ε)))
        (inrDeriv cc C A (⊤ : ε))
      simp only [atIndex_compose] at hd
      have hl := action_inl (R := R) (B := A) cc (atZeroDeriv (input A) hg)
      have he := Equates.case cc (QCtx.Split.zero_left (input A)) (Equates.refl (R := R) ⟨hf⟩)
        hl (Equates.refl (R := R) ⟨atZeroDeriv (input A) (inrDeriv cc C A (⊤ : ε))⟩)
      apply Equates.trans _ he
      simpa only [composeArrow, composeTerm, descArrow, inlArrow, inrArrow,
        continuation_atIndex, atIndex_compose, action] using hd
    exact (Quotient.sound hn).trans (congrArg (iterate hR cap) (Quotient.sound hc).symm)

theorem iterate_codiagonal (hR : R.RenamingClosed) (cap : F.HasIter)
    (f : Hom (ε := ε) F R A (coprod (coprod B A) A)) :
    iterate hR cap (iterate hR cap f) = iterate hR cap
      (compose hR f (desc hR (iter_hasCase cap) (identity (coprod B A))
        (inr (iter_hasCase cap) B A))) := by
  induction f using Quotient.inductionOn with
  | _ f =>
    obtain ⟨hf⟩ := f.property
    let cc := iter_hasCase cap
    let c : Arrow (Φ := Φ) (ε := ε) F A (coprod B A) :=
      ⟨.case f.val (.bv 0) (.inr (.bv 0)),
        ⟨.case cc (QCtx.Split.zero_left (input A)) hf
          (atZeroDeriv (input A) (identityDeriv (coprod B A) ⊤))
          (atZeroDeriv (input A) (inrDeriv cc B A ⊤))⟩⟩
    have hn : Equates (ε := ε) F R (input A)
        (iterateArrow cap (iterateArrow cap f)).val (iterateArrow cap c).val B := by
      apply Equates.ofAxiom _ (iterateArrow cap (iterateArrow cap f)).property
        (iterateArrow cap c).property
      have law := EquationAxiom.codiagonal (ε := ε) cap
        (QCtx.Split.zero_left (input A)) (input A).zero_linearity
        EffectSystem.iterable_top (identityDeriv A (⊤ : ε)) (atZeroDeriv (input A) hf)
      simpa only [iterateArrow, iterateTerm, c, continuation_atIndex,
        underBinder_atIndex_zero, atIndex, Tm.rename, Tm.underBinder,
        Tm.rename_comp, Tm.up, Fin.cases_zero] using law
    have hc : Equates (ε := ε) F R (input A)
        (composeArrow f (descArrow cc (identityArrow (coprod B A)) (inrArrow cc B A))).val
        c.val (coprod B A) := by
      simpa only [composeArrow, composeTerm, descArrow, identityArrow, inrArrow,
        continuation_atIndex, c, action, atIndex, Tm.rename] using
        (action_desc (R := R) cc hf (identityDeriv (coprod B A) (⊤ : ε))
          (inrDeriv cc B A (⊤ : ε)))
    exact (Quotient.sound hn).trans (congrArg (iterate hR cap) (Quotient.sound hc).symm)


/-- The native iteration operation satisfies the three Conway equations. -/
def conwayIteration (hR : R.RenamingClosed) (cap : F.HasIter) :
    letI := category (ε := ε) F R hR
    ConwayIteration τ (chosenCoproducts (ε := ε) (F := F) (R := R) hR (iter_hasCase cap)) := by
  let := category (ε := ε) F R hR
  refine { iterate := iterate hR cap
           fixpoint := iterate_fixpoint hR cap
           naturality := ?_
           codiagonal := iterate_codiagonal hR cap }
  intro A B C f g
  change compose hR (iterate hR cap f) g = iterate hR cap
    (compose hR f (desc hR (iter_hasCase cap)
      (compose hR g (inl (iter_hasCase cap) C A))
      (compose hR (identity A) (inr (iter_hasCase cap) C A))))
  rw [identity_compose]
  exact iterate_naturality hR cap f g

end Silmaril.Isotope.Refinement.Models.Syntactic
