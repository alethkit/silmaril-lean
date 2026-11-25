module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlWitnessCoherence
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseSoundness
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ProductEquations
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterConwaySoundness
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterCodiagonal
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterNaturalitySoundness

/-! # Soundness of all written iteration equations -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Every iteration equation holds for every endpoint derivation, even when their
hidden intermediate types and effect bounds differ. -/
theorem denoteIter_equation (M : IterModel.{u,v,w,r} (Ty α) Φ ε)
    {n : Nat} {Γ : QCtx (Ty α) n} {a b : Term Φ n} {A : Ty α}
    {e e' : ε} (h : EquationAxiom (ε := ε) .iter Γ a b A)
    (ha : HasType .iter Γ e a A) (hb : HasType .iter Γ e' b A) :
    denoteIter M ha = denoteIter M hb := by
  let K := ControlData.iter M
  have N := ControlEnvironment.iter M
  have H : WitnessCoherent M.toSeqModel K := Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent M
  cases h with
  | letOp s hf harg hc => exact Sequential.denote_letOp M.toSeqModel K N H s hf harg hc ha hb
  | letLet s t harg hc hd => exact Sequential.denote_letLet M.toSeqModel K N H s t harg hc hd ha hb
  | letLetPair s t harg hc hd => exact Sequential.denote_letLetPair M.toSeqModel K N H s t harg hc hd ha hb
  | letCase cap s t harg hl hr hd =>
    obtain ⟨k, hk⟩ := denote_letCase_exists M.toCaseData (F := .iter) (fun _ => M.iterate) N cap s t harg hl hr hd
    exact (H ha _).trans (hk.trans (H k hb))
  | pairBind s harg hc => exact Sequential.denote_pairBind M.toSeqModel K N H s harg hc ha hb
  | caseBind cap s harg hl hr =>
    obtain ⟨k, hk⟩ := denote_caseBind_exists M.toCaseData (F := .iter) (fun _ => M.iterate) N cap s harg hl hr
    exact (H ha _).trans (hk.trans (H k hb))
  | iterBind cap s hu hi harg hc =>
    obtain ⟨k, hk⟩ := denote_iterBind_exists M.toCaseData (F := .iter) (fun _ => M.iterate) N
      cap s hu hi harg hc
    exact (H ha _).trans (hk.trans (H k hb))
  | term harg => exact (Sequential.denote_term M.toSeqModel K H harg ha).trans (H harg hb)
  | initial cap s harg hl hr =>
    exact (H ha _).trans ((denote_initial M.toCaseData (F := .iter) (fun _ => M.iterate) cap s harg hl hr).trans (H _ hb))
  | pairEta harg => exact (Sequential.denote_pairEta M.toSeqModel K N H harg ha).trans (H harg hb)
  | pairBeta s t hleft hright hc => exact Sequential.denote_pairBeta M.toSeqModel K N H s t hleft hright hc ha hb
  | caseBetaL cap s harg hl hr =>
    exact (H ha _).trans ((denote_caseBetaL M.toCaseData (F := .iter) (fun _ => M.iterate) cap s harg hl hr).trans (H _ hb))
  | caseBetaR cap s harg hl hr =>
    exact (H ha _).trans ((denote_caseBetaR M.toCaseData (F := .iter) (fun _ => M.iterate) cap s harg hl hr).trans (H _ hb))
  | caseEta cap harg =>
    exact (H ha _).trans ((denote_caseEta M.toCaseData (F := .iter) (fun _ => M.iterate) cap harg).trans (H harg hb))
  | fixpoint _ s hu hi harg hc =>
    obtain ⟨k, hk⟩ := denoteIter_fixpoint_exists M s hu hi harg hc
    exact (H ha _).trans (hk.trans (H k hb))
  | naturality _ s t hu hv harg hc hd =>
    exact denoteIter_naturality_equation M s t hu hv harg hc hd ha hb
  | codiagonal _ s hu hi harg hc =>
    exact denoteIter_codiagonal M s hu hi harg hc ha hb

end Silmaril.Isotope.Refinement.Models.Denotation
