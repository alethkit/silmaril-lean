module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.StructuralActs

/-! # Native action of quantitative context splitting -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Packing remains quantity-bounded after inserting an omitted slot. -/
theorem pack_lift_bound {n : Nat} {Γ : QCtx τ n} (h : Γ.DefaultAnnotations) (A : τ) :
    quantity (packed Γ) ≤ (Γ.snoc A .zero).linearity := by
  rw [QCtx.linearity_snoc, Usage.linearity_zero]
  change quantity (packed Γ) ≤ ⊤ ⊓ Γ.linearity
  rw [top_inf_eq, packed_quantity_eq h]

/-- The isolated default parameter has precisely its intrinsic quantity. -/
theorem zero_parameter_bound {n : Nat} (Γ : QCtx τ n) (A : τ) :
    quantity A ≤ (Γ.zero.snoc A).linearity := by
  rw [QCtx.linearity_snoc, QCtx.zero_linearity, Usage.linearity_used, inf_top_eq, inf_top_eq]

theorem splitSlot_acts (hR : R.RenamingClosed) {n : Nat} {Γ Γl Γr : QCtx τ n}
    (s : Γ.Split Γl Γr) (hΓ : Γ.DefaultAnnotations) (A : τ)
    {q ql qr : Usage} (hq : q = .zero ∨ q = .used ⊤)
    (hs : QCtx.SlotSplit A q ql qr)
    (f : PureHom (seqData (ε := ε) (F := F) (R := R) hR) (packed Γ) (product (packed Γl) (packed Γr)))
    (hf : Acts Γ (packTerm Γ) f.val (.pair (packTerm Γl) (packTerm Γr))) :
    Acts (Γ.snoc A q) (packTerm (Γ.snoc A q))
      (splitSlot (seqData (ε := ε) (F := F) (R := R) hR) f hs).val
      (.pair (packTerm (Γl.snoc A ql)) (packTerm (Γr.snoc A qr))) := by
  have hl := hΓ.split_left s
  have hr := hΓ.split_right s
  have hi := hf.rename hR Fin.succ (QCtx.Weakening.insertZero Γ A)
  have da := (packDeriv (F := F) (Φ := Φ) Γl (⊥ : ε)).rename Fin.succ (.insertZero Γl A)
  have db := (packDeriv (F := F) (Φ := Φ) Γr (⊥ : ε)).rename Fin.succ (.insertZero Γr A)
  have dp := (packDeriv (F := F) (Φ := Φ) Γ (⊥ : ε)).rename Fin.succ (.insertZero Γ A)
  have dv := zeroParameter (F := F) (Φ := Φ) Γ A (.used ⊤) (⊥ : ε) (by
    change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
    exact inf_le_inf bot_le le_rfl)
  have st := s.snoc (A := A) (.left .zero)
  have ss := (QCtx.Split.zero_right Γ).snoc (A := A) (.right (.used ⊤))
  have qa := pack_lift_bound hl A
  have qb := pack_lift_bound hr A
  have qv := zero_parameter_bound Γ A
  have heRight := seqData_right (ε := ε) (F := F) (R := R) hR f.val A
  have hright := hi.right hR ss dp.top dv qv
  have hassoc := Acts.assoc (R := R) ss st da db dv qa qb qv
  cases hs with
  | left =>
    rcases hq with rfl | rfl
    · simpa only [splitSlot, retain, packTerm_snoc_zero, Tm.rename, Tm.lift] using hi
    · obtain ⟨Γra, sl, sr⟩ := ss.swapAssoc st.symm
      have hb := (Acts.swap (R := R) sr db dv.top qb).left hR sl.symm da.top (HasType.pair sr db dv).top
      have hc := Acts.assocInv (R := R) sl.symm sr.symm da dv db qa qv qb
      have hbc := hb.compose hR (HasType.pair sl.symm da (.pair sr db dv)).top hc
      have habc := hassoc.compose hR (HasType.pair ss (.pair st da db) dv).top hbc
      have hall := hright.compose hR (HasType.pair ss dp dv).top habc
      simp only [splitSlot, retain, pureCompose, heRight, pureRight, pureLeft, seqData_compose,
        seqData_left, seqData_associator, seqData_associatorInv, seqData_braiding,
        packTerm_snoc_used, packTerm_snoc_zero, Tm.lift]
      exact hall
  | right =>
    rcases hq with rfl | rfl
    · simpa only [splitSlot, retain, packTerm_snoc_zero, Tm.rename, Tm.lift] using hi
    · have hall := hright.compose hR (HasType.pair ss dp dv).top hassoc
      simp only [splitSlot, retain, pureCompose, heRight, pureRight, seqData_compose,
        seqData_associator, packTerm_snoc_used, packTerm_snoc_zero, Tm.lift]
      exact hall
  | both hc =>
    rcases hq with rfl | rfl
    · cases hc
    · have hA : Quantity.relevant ≤ quantity A := by
        change Usage.used Quantity.relevant ≤ Usage.used (⊤ ⊓ quantity A) at hc
        simpa only [Usage.used_le_used, top_inf_eq] using hc
      have hv := Acts.copy (R := R) dv hA qv
      have ht := hi.tensor hR ss dp.top dv qv hv
      have hm := Acts.middleSwap (R := R) ss st (QCtx.Split.diagonal _ (hA.trans qv))
        da db dv dv qa qb qv qv
      have hall := ht.compose hR (HasType.pair ss dp dv).top hm
      simp only [splitSlot, retain, pureCompose, heRight, pureTensor, SeqData.tensor, seqData_compose,
        seqData_left, seqData_copy, seqData_middleSwap,
        packTerm_snoc_used, Tm.lift]
      exact hall

/-- The interpreted context splitter produces precisely the two native packed
subcontexts. Duplication uses only the source split's quantity permission. -/
theorem split_acts (hR : R.RenamingClosed) {n : Nat} {Γ Γl Γr : QCtx τ n}
    (s : Γ.Split Γl Γr) (hΓ : Γ.DefaultAnnotations) :
    Acts Γ (packTerm Γ) (split (seqData (ε := ε) (F := F) (R := R) hR) s)
      (.pair (packTerm Γl) (packTerm Γr)) := by
  induction n with
  | zero =>
    have h := Acts.leftUnitInv (R := R) (packDeriv (F := F) (Φ := Φ) Γ (⊥ : ε))
      (packed_quantity_eq hΓ).le
    simp only [split, splitPure, seqData_leftUnitorInv]
    exact h
  | succ n ih =>
    let Γt : QCtx τ n := fun i => Γ i.succ
    let Γlt : QCtx τ n := fun i => Γl i.succ
    let Γrt : QCtx τ n := fun i => Γr i.succ
    have st : Γt.Split Γlt Γrt := fun i => s i.succ
    have hl : Γlt.snoc (Γ 0).1 (Γl 0).2 = Γl := by
      rw [← (s 0).1]
      exact QCtx.snoc_tail Γl
    have hr : Γrt.snoc (Γ 0).1 (Γr 0).2 = Γr := by
      rw [← (s 0).2.1]
      exact QCtx.snoc_tail Γr
    have he := splitSlot_acts (F := F) (R := R) (ε := ε) hR st hΓ.tail (Γ 0).1
      (hΓ 0) (s 0).2.2 (splitPure (seqData hR) st) (ih st hΓ.tail)
    let P (p : QCtx τ (n + 1) × QCtx τ (n + 1) × QCtx τ (n + 1)) :=
      ∀ k : p.1.Split p.2.1 p.2.2,
        Acts p.1 (packTerm p.1) (split (seqData (ε := ε) (F := F) (R := R) hR) k)
          (.pair (packTerm p.2.1) (packTerm p.2.2))
    have hall : P (Γt.snoc (Γ 0).1 (Γ 0).2,
        Γlt.snoc (Γ 0).1 (Γl 0).2, Γrt.snoc (Γ 0).1 (Γr 0).2) := by
      intro k
      exact he
    have hΓeq : Γt.snoc (Γ 0).1 (Γ 0).2 = Γ := QCtx.snoc_tail Γ
    exact ((congrArg P (congrArg₂ Prod.mk hΓeq (congrArg₂ Prod.mk hl hr))).mp hall) s

end Silmaril.Isotope.Refinement.Models.Syntactic
