module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.CaseEquations
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Renaming

/-! # Sound case equations on canonical typing witnesses

These equations hold in every categorical case model, also when its terms use
an iteration interface. They do not assume typing coherence: binder equations
construct actual endpoint witnesses with the required interpretation.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation

open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (it : F.HasIter → ∀ {A B : τ}, M.Hom A (coprod B A) → M.Hom A B)
local notation "K" => ControlData.ofCase M F it

set_option backward.isDefEq.respectTransparency false in
/-- Left case beta preserves the effectful scrutinee and selects its branch. -/
theorem denote_caseBetaL {n : Nat} {Γ Γl Γr : QCtx τ n} {e : ε}
    {a : Term Φ n} {l r : Term Φ (n + 1)} {A B C : τ}
    (cap : F.HasCase) (s : Γ.Split Γl Γr) (ha : HasType F Γr e a A)
    (hl : HasType F (Γl.snoc A) e l C) (hr : HasType F (Γl.snoc B) e r C) :
    denote M.toSeqData K (.case cap s (.inl cap ha) hl hr) =
      denote M.toSeqData K (.let₁ s ha hl) := by
  change M.compose (split M.toSeqData s)
    (M.compose (M.left (packed Γl) (M.compose (denote M.toSeqData K ha) (M.inl A B)))
      (M.compose (M.distribute (packed Γl) A B)
        (M.desc (denote M.toSeqData K hl) (denote M.toSeqData K hr)))) = _
  rw [M.toSeqData.left_compose, M.compose_assoc,
    ← M.compose_assoc (M.left (packed Γl) (M.inl A B)), M.left_inl_distribute, M.inl_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Right case beta preserves the effectful scrutinee and selects its branch. -/
theorem denote_caseBetaR {n : Nat} {Γ Γl Γr : QCtx τ n} {e : ε}
    {a : Term Φ n} {l r : Term Φ (n + 1)} {A B C : τ}
    (cap : F.HasCase) (s : Γ.Split Γl Γr) (ha : HasType F Γr e a B)
    (hl : HasType F (Γl.snoc A) e l C) (hr : HasType F (Γl.snoc B) e r C) :
    denote M.toSeqData K (.case cap s (.inr cap ha) hl hr) =
      denote M.toSeqData K (.let₁ s ha hr) := by
  change M.compose (split M.toSeqData s)
    (M.compose (M.left (packed Γl) (M.compose (denote M.toSeqData K ha) (M.inr A B)))
      (M.compose (M.distribute (packed Γl) A B)
        (M.desc (denote M.toSeqData K hl) (denote M.toSeqData K hr)))) = _
  rw [M.toSeqData.left_compose, M.compose_assoc,
    ← M.compose_assoc (M.left (packed Γl) (M.inr A B)), M.left_inr_distribute, M.inr_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Canonical case eta returns the original result without removing effects. -/
theorem denote_caseEta {n : Nat} {Γ : QCtx τ n} {e : ε}
    {a : Term Φ n} {A B : τ} (cap : F.HasCase) (ha : HasType F Γ e a (coprod A B)) :
    denote M.toSeqData K
      (.case cap (QCtx.Split.zero_left Γ) ha
        (.inl cap (.var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) A)))
        (.inr cap (.var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) B)))) =
      denote M.toSeqData K ha := by
  change M.compose (split M.toSeqData (QCtx.Split.zero_left Γ))
    (M.compose (M.left (packed Γ.zero) (denote M.toSeqData K ha))
      (M.compose (M.distribute (packed Γ.zero) A B)
        (M.desc
          (M.compose (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γ)) A)
            (M.leftUnitor A)) (M.inl A B))
          (M.compose (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γ)) B)
            (M.leftUnitor B)) (M.inr A B))))) = _
  rw [M.case_eta]
  exact zero_context_bind M.toSeqModel Γ _ _

set_option backward.isDefEq.respectTransparency false in
/-- An empty scrutinee makes its continuation irrelevant, including a linear
retained environment. Binary distributivity supplies uniqueness from `D × 0`. -/
theorem denote_initial {n : Nat} {Γ Γl Γr : QCtx τ n} {e : ε}
    {a : Term Φ n} {b c : Term Φ (n + 1)} {A B : τ}
    (cap : F.HasCase) (s : Γ.Split Γl Γr) (ha : HasType F Γr e a Silmaril.empty)
    (hb : HasType F (Γl.snoc A) e b B) (hc : HasType F (Γl.snoc A) e c B) :
    denote M.toSeqData K (.let₁ s (.abort cap ha) hb) =
      denote M.toSeqData K (.let₁ s (.abort cap ha) hc) := by
  change M.compose (split M.toSeqData s)
      (M.compose (M.left (packed Γl) (M.compose (denote M.toSeqData K ha) (M.abort A)))
        (denote M.toSeqData K hb)) =
    M.compose (split M.toSeqData s)
      (M.compose (M.left (packed Γl) (M.compose (denote M.toSeqData K ha) (M.abort A)))
        (denote M.toSeqData K hc))
  simp only [M.toSeqData.left_compose, M.compose_assoc]
  exact congrArg (fun k => M.compose (split M.toSeqData s)
    (M.compose (M.left (packed Γl) (denote M.toSeqData K ha)) k))
      (M.empty_tensor_hom_ext _ _)

/-- A compatible zero-use insertion witness contributes no semantic wire. -/
theorem denote_underBinder_zero_exists (N : ControlEnvironment K)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ (n + 1)} {A B C : τ}
    (h : HasType F (Γ.snoc B) e t C) :
    ∃ k : HasType F ((Γ.snoc A .zero).snoc B) e t.underBinder C,
      denote M.toSeqData K k = denote M.toSeqData K h := by
  let w := (QCtx.Weakening.insertZero Γ A).up (A := B)
  obtain ⟨k, hk⟩ := denote_rename_exists M.toSeqModel K N h _ w
  refine ⟨k, hk.trans ?_⟩
  have hw : weaken M.toSeqData w = M.identity (product (packed Γ) B) := by
    change M.right (weaken M.toSeqData (QCtx.Weakening.insertZero Γ A)) B = _
    have hz : weaken M.toSeqData (QCtx.Weakening.insertZero Γ A) = M.identity (packed Γ) :=
      (congrArg Subtype.val (weakenPure_skip M.toSeqModel (QCtx.Weakening.refl Γ)
        (A := A) (q := .zero) le_rfl)).trans (weaken_refl M.toSeqData Γ)
    rw [hz]
    exact M.toSeqData.right_identity _ _
  rw [hw]
  exact M.identity_compose _

set_option backward.isDefEq.respectTransparency false in
/-- The semantic case binder factors through let, with a constructed endpoint
witness. No global typing-coherence theorem is used. -/
theorem denote_caseBind_exists (N : ControlEnvironment K)
    {n : Nat} {Γ Γl Γr : QCtx τ n} {e : ε}
    {a : Term Φ n} {l r : Term Φ (n + 1)} {A B C : τ}
    (cap : F.HasCase) (s : Γ.Split Γl Γr) (ha : HasType F Γr e a (coprod A B))
    (hl : HasType F (Γl.snoc A) e l C) (hr : HasType F (Γl.snoc B) e r C) :
    ∃ k : HasType F Γ e (.let₁ a (.case (.bv 0) l.underBinder r.underBinder)) C,
      denote M.toSeqData K (.case cap s ha hl hr) = denote M.toSeqData K k := by
  obtain ⟨kl, hkl⟩ := denote_underBinder_zero_exists M it N (A := coprod A B) hl
  obtain ⟨kr, hkr⟩ := denote_underBinder_zero_exists M it N (A := coprod A B) hr
  let hv : HasType F (Γl.zero.snoc (coprod A B)) e (.bv 0 : Term Φ (n + 1)) (coprod A B) :=
    .var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γl) (coprod A B))
  let si := (QCtx.Split.zero_right Γl).snoc (.right (.used ⊤)) (A := coprod A B)
  let ki := HasType.case cap si hv kl kr
  refine ⟨.let₁ s ha ki, ?_⟩
  have hi : denote M.toSeqData K ki =
      M.compose (M.distribute (packed Γl) A B)
        (M.desc (denote M.toSeqData K hl) (denote M.toSeqData K hr)) := by
    change M.compose (split M.toSeqData si)
      (M.compose (M.left (packed Γl) (denote M.toSeqData K hv))
        (M.compose (M.distribute (packed Γl) A B)
          (M.desc (denote M.toSeqData K kl) (denote M.toSeqData K kr)))) = _
    rw [hkl, hkr, ← M.compose_assoc]
    change M.compose (M.compose (split M.toSeqData si)
      (M.left (packed Γl) (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γl)) (coprod A B))
        (M.leftUnitor (coprod A B))))) _ = _
    rw [newest_split_variable M.toSeqModel Γl (coprod A B) (QCtx.zero_discardable Γl)]
    exact M.identity_compose _
  change M.compose (split M.toSeqData s)
    (M.compose (M.left (packed Γl) (denote M.toSeqData K ha)) _) =
      M.compose (split M.toSeqData s)
        (M.compose (M.left (packed Γl) (denote M.toSeqData K ha)) (denote M.toSeqData K ki))
  rw [hi]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- A following effectful continuation distributes into the two branches.
The result includes compatible typing witnesses for both inserted binders. -/
theorem denote_letCase_exists (N : ControlEnvironment K)
    {n : Nat} {Γ Γl Γm Γr Γc : QCtx τ n} {e : ε}
    {a : Term Φ n} {l r d : Term Φ (n + 1)} {A B C D : τ}
    (cap : F.HasCase) (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
    (ha : HasType F Γm e a (coprod A B))
    (hl : HasType F (Γl.snoc A) e l C) (hr : HasType F (Γl.snoc B) e r C)
    (hd : HasType F (Γr.snoc C) e d D) :
    ∃ k : HasType F Γ e (.case a (.let₁ l d.underBinder) (.let₁ r d.underBinder)) D,
      denote M.toSeqData K (.let₁ outer.symm (.case cap inner ha hl hr) hd) =
        denote M.toSeqData K k := by
  obtain ⟨Γlr, whole, rest⟩ := outer.swapAssoc inner
  obtain ⟨kdl, hdl⟩ := denote_underBinder_zero_exists M it N (A := A) hd
  obtain ⟨kdr, hdr⟩ := denote_underBinder_zero_exists M it N (A := B) hd
  let sl := rest.symm.snoc (.right (.used ⊤)) (A := A)
  let sr := rest.symm.snoc (.right (.used ⊤)) (A := B)
  let kl := HasType.let₁ sl hl kdl
  let kr := HasType.let₁ sr hr kdr
  refine ⟨.case cap whole ha kl kr, ?_⟩
  have hkl : denote M.toSeqData K kl =
      M.compose (M.right (split M.toSeqData rest.symm) A)
        (M.compose (M.associator (packed Γr) (packed Γl) A)
          (M.compose (M.left (packed Γr) (denote M.toSeqData K hl)) (denote M.toSeqData K hd))) := by
    change M.compose (M.compose (M.right (split M.toSeqData rest.symm) A)
      (M.associator (packed Γr) (packed Γl) A))
      (M.compose (M.left (packed Γr) (denote M.toSeqData K hl)) (denote M.toSeqData K kdl)) = _
    rw [hdl, M.compose_assoc]
  have hkr : denote M.toSeqData K kr =
      M.compose (M.right (split M.toSeqData rest.symm) B)
        (M.compose (M.associator (packed Γr) (packed Γl) B)
          (M.compose (M.left (packed Γr) (denote M.toSeqData K hr)) (denote M.toSeqData K hd))) := by
    change M.compose (M.compose (M.right (split M.toSeqData rest.symm) B)
      (M.associator (packed Γr) (packed Γl) B))
      (M.compose (M.left (packed Γr) (denote M.toSeqData K hr)) (denote M.toSeqData K kdr)) = _
    rw [hdr, M.compose_assoc]
  change M.compose (split M.toSeqData outer.symm)
      (M.compose (M.left (packed Γr)
        (M.compose (split M.toSeqData inner)
          (M.compose (M.left (packed Γl) (denote M.toSeqData K ha))
            (M.compose (M.distribute (packed Γl) A B)
              (M.desc (denote M.toSeqData K hl) (denote M.toSeqData K hr))))))
        (denote M.toSeqData K hd)) =
    M.compose (split M.toSeqData whole)
      (M.compose (M.left (packed Γlr) (denote M.toSeqData K ha))
        (M.compose (M.distribute (packed Γlr) A B)
          (M.desc (denote M.toSeqData K kl) (denote M.toSeqData K kr))))
  rw [hkl, hkr, ← M.compose_assoc, split_bind_assoc M.toSeqModel whole rest.symm outer.symm inner]
  simp only [M.compose_assoc]
  rw [M.case_bind (E := packed Γr) (D := packed Γl) (A := A) (B := B) (C := C) (G := D) (denote M.toSeqData K hl) (denote M.toSeqData K hr) (denote M.toSeqData K hd)]
  rw [ControlEnvironment.caseData_natural M (split M.toSeqData rest.symm)]

end Silmaril.Isotope.Refinement.Models.Denotation
