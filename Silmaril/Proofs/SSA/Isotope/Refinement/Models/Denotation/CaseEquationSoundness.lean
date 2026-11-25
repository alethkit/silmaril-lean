module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlWitnessCoherence
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseSoundness
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ProductEquations
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Elimination

/-! # Soundness of all written case equations -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Every case equation holds for every endpoint derivation, even when their
hidden intermediate types and effect bounds differ. -/
theorem denoteCase_equation (M : CaseModel.{u,v,w,r} (Ty α) Φ ε)
    {n : Nat} {Γ : QCtx (Ty α) n} {a b : Term Φ n} {A : Ty α}
    {e e' : ε} (h : EquationAxiom (ε := ε) .case Γ a b A)
    (ha : HasType .case Γ e a A) (hb : HasType .case Γ e' b A) :
    denoteCase M ha = denoteCase M hb := by
  let K := ControlData.case M
  have N := ControlEnvironment.case M
  have H : WitnessCoherent M.toSeqModel K := Silmaril.Proofs.SSA.Isotope.Refinement.caseWitnessCoherent M
  cases h with
  | letOp s hf harg hc => exact Sequential.denote_letOp M.toSeqModel K N H s hf harg hc ha hb
  | letLet s t harg hc hd => exact Sequential.denote_letLet M.toSeqModel K N H s t harg hc hd ha hb
  | letLetPair s t harg hc hd => exact Sequential.denote_letLetPair M.toSeqModel K N H s t harg hc hd ha hb
  | letCase cap s t harg hl hr hd =>
    obtain ⟨k, hk⟩ := denote_letCase_exists M.toCaseData (F := .case) (fun cap => False.elim cap) N cap s t harg hl hr hd
    exact (H ha _).trans (hk.trans (H k hb))
  | pairBind s harg hc => exact Sequential.denote_pairBind M.toSeqModel K N H s harg hc ha hb
  | caseBind cap s harg hl hr =>
    obtain ⟨k, hk⟩ := denote_caseBind_exists M.toCaseData (F := .case) (fun cap => False.elim cap) N cap s harg hl hr
    exact (H ha _).trans (hk.trans (H k hb))
  | iterBind cap => exact False.elim cap
  | term harg => exact (Sequential.denote_term M.toSeqModel K H harg ha).trans (H harg hb)
  | initial cap s harg hl hr =>
    exact (H ha _).trans ((denote_initial M.toCaseData (F := .case) (fun cap => False.elim cap) cap s harg hl hr).trans (H _ hb))
  | pairEta harg => exact (Sequential.denote_pairEta M.toSeqModel K N H harg ha).trans (H harg hb)
  | pairBeta s t hleft hright hc => exact Sequential.denote_pairBeta M.toSeqModel K N H s t hleft hright hc ha hb
  | caseBetaL cap s harg hl hr =>
    exact (H ha _).trans ((denote_caseBetaL M.toCaseData (F := .case) (fun cap => False.elim cap) cap s harg hl hr).trans (H _ hb))
  | caseBetaR cap s harg hl hr =>
    exact (H ha _).trans ((denote_caseBetaR M.toCaseData (F := .case) (fun cap => False.elim cap) cap s harg hl hr).trans (H _ hb))
  | caseEta cap harg =>
    exact (H ha _).trans ((denote_caseEta M.toCaseData (F := .case) (fun cap => False.elim cap) cap harg).trans (H harg hb))
  | fixpoint cap => exact False.elim cap
  | naturality cap => exact False.elim cap
  | codiagonal cap => exact False.elim cap

/-- Directed elimination also applies to case terms with arbitrary retained resources. -/
theorem denoteCase_eliminate (M : CaseModel.{u,v,w,r} (Ty α) Φ ε)
    (p : Polarity) {n : Nat} {Γ Γl : QCtx (Ty α) n}
    {e η eL eR : ε} {a b : Term Φ n} {B : Ty α}
    (s : Γ.Split Γl Γ) (ha : HasType .case Γl e a Silmaril.unit)
    (hd : Usage.zero ≤ Usage.used (EffectSystem.quantity p e)) (hb : HasType .case Γ η b B)
    (hl : HasType .case Γ eL (.let₁ a b.lift) B)
    (hr : HasType .case Γ eR (.let₁ .unit b.lift) B) :
    p.orient M.le (denoteCase M hl) (denoteCase M hr) :=
  Sequential.denote_eliminate M.toSeqModel (ControlData.case M) (ControlEnvironment.case M)
    (Silmaril.Proofs.SSA.Isotope.Refinement.caseWitnessCoherent M) (ControlEffects.case M) p s ha hd hb hl hr

/-- Directed elimination for iteration terms uses the same resource law. -/
theorem denoteIter_eliminate (M : IterModel.{u,v,w,r} (Ty α) Φ ε)
    (p : Polarity) {n : Nat} {Γ Γl : QCtx (Ty α) n}
    {e η eL eR : ε} {a b : Term Φ n} {B : Ty α}
    (s : Γ.Split Γl Γ) (ha : HasType .iter Γl e a Silmaril.unit)
    (hd : Usage.zero ≤ Usage.used (EffectSystem.quantity p e)) (hb : HasType .iter Γ η b B)
    (hl : HasType .iter Γ eL (.let₁ a b.lift) B)
    (hr : HasType .iter Γ eR (.let₁ .unit b.lift) B) :
    p.orient M.le (denoteIter M hl) (denoteIter M hr) :=
  Sequential.denote_eliminate M.toSeqModel (ControlData.iter M) (ControlEnvironment.iter M)
    (Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent M) (ControlEffects.iter M) p s ha hd hb hl hr

end Silmaril.Isotope.Refinement.Models.Denotation
