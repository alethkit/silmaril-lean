module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterSoundness
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationNaturalityBody
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlWitnessCoherence
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IdentityBinding
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.IterUniformitySoundness

/-! # The native endpoint of written iteration naturality -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- Actual typing and denotation of the case body on the right of naturality. -/
theorem denoteIter_naturalityBody_exists {n : Nat} {Γp Γl Γm : QCtx τ n} {e : ε}
    {b c : Term Φ (n + 1)} {A B C : τ}
    (rest : Γp.Split Γl Γm) (hul : Γl.linearity = ⊤)
    (hb : HasType .iter (Γm.snoc A) e b (coprod B A))
    (hc : HasType .iter (Γl.snoc B) e c C)
    (dE : Quantity.affine ≤ quantity (packed Γl)) :
    ∃ k : HasType .iter (Γp.snoc A) e
      (.case b (.inl c.underBinder) (.inr (.bv 0))) (coprod C A),
      denoteIter M k = M.compose (M.right (split M.toSeqData rest) A)
        (M.naturalityBody dE (denoteIter M hb) (denoteIter M hc)) := by
  obtain ⟨kc, hkc⟩ := denote_underBinder_zero_exists M.toCaseData (fun _ => M.iterate)
    (ControlEnvironment.iter M) (A := A) hc
  have hd : (Γl.snoc A .zero).Discardable := by
    apply QCtx.discardable_iff_linearity.mpr
    rw [QCtx.linearity_snoc, Usage.linearity_zero, hul, inf_top_eq]
    exact le_top
  let kv := HasType.var (F := .iter) (Φ := Φ) (e := e) 0 (QCtx.varAllowed_snoc hd A)
  let ss := rest.snoc (.right (.used ⊤)) (A := A)
  let kk := HasType.case (F := .iter) trivial ss hb (.inl trivial kc) (.inr trivial kv)
  refine ⟨kk, ?_⟩
  change M.compose (M.compose (M.right (split M.toSeqData rest) A)
      (M.associator (packed Γl) (packed Γm) A))
    (M.compose (M.left (packed Γl) (denoteIter M hb))
      (M.compose (M.distribute (packed Γl) B A)
        (M.desc (M.compose (denoteIter M kc) (M.inl C A))
          (M.compose (M.compose (M.right (discard M.toSeqData hd) A) (M.leftUnitor A)) (M.inr C A))))) = _
  change denoteIter M kc = denoteIter M hc at hkc
  rw [hkc, M.compose_assoc]
  rfl



end Silmaril.Isotope.Refinement.Models.Denotation

namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} (Ty α) Φ ε)

/-- Written naturality follows from directed uniformity in both polarities,
using the pure identity state comparison. This is a rule-admissibility proof,
not an extra Conway axiom imposed on the semantic model. -/
theorem denoteIter_naturality_equation
    {n : Nat} {Γ Γl Γm Γr Γc : QCtx (Ty α) n} {e eL eR : ε}
    {a : Term Φ n} {b c : Term Φ (n + 1)} {A B C : Ty α}
    (outer : Γ.Split Γl Γc) (inner : Γc.Split Γm Γr)
    (hul : Γl.linearity = ⊤) (hum : Γm.linearity = ⊤)
    (ha : HasType .iter Γr e a A) (hb : HasType .iter (Γm.snoc A) e b (coprod B A))
    (hc : HasType .iter (Γl.snoc B) e c C)
    (hl : HasType .iter Γ eL (.let₁ (.iter a b) c) C)
    (hr : HasType .iter Γ eR (.iter a (.case b (.inl c.underBinder) (.inr (.bv 0)))) C) :
    denoteIter M hl = denoteIter M hr := by
  obtain ⟨Γp, whole, rest⟩ := outer.assoc inner
  have hup : Γp.linearity = ⊤ := top_le_iff.mp (rest.le_linearity (hul ▸ le_rfl) (hum ▸ le_rfl))
  have hdl : Γl.Discardable := QCtx.discardable_iff_linearity.mpr (hul ▸ le_top)
  have hdm : Γm.Discardable := QCtx.discardable_iff_linearity.mpr (hum ▸ le_top)
  have hdp : Γp.Discardable := QCtx.discardable_iff_linearity.mpr (hup ▸ le_top)
  have wb : QCtx.Weakening (Γp.snoc A) (Γm.snoc A) id := by
    convert (rest.weakenRight hdl).up A using 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have wc : QCtx.Weakening (Γp.snoc B) (Γl.snoc B) id := by
    convert (rest.weakenLeft hdm).up B using 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  let hbP : HasType .iter (Γp.snoc A) (⊤ : ε) b (coprod B A) :=
    Tm.rename_id b ▸ hb.top.rename id wb
  let hcP : HasType .iter (Γp.snoc B) (⊤ : ε) c C :=
    Tm.rename_id c ▸ hc.top.rename id wc
  let diagonal := QCtx.Split.diagonal Γp (hup ▸ le_top)
  let hs : HasType .iter (Γp.snoc A) (⊥ : ε) (.bv 0 : Term Φ (n+1)) A :=
    .var 0 (QCtx.varAllowed_snoc hdp A)
  obtain ⟨hbnew, _⟩ := denoteIter_naturalityBody_exists M diagonal hup hbP hcP
    (discardable_quantity hdp)
  obtain ⟨hpre, hepre⟩ := denote_identityBind_exists M.toCaseData (fun _ => M.iterate)
    (ControlEnvironment.iter M) hbnew
  obtain ⟨hleft, heleft⟩ := denote_iterBind_exists M.toCaseData (fun _ => M.iterate)
    (ControlEnvironment.iter M) trivial whole hup EffectSystem.iterable_top ha.top hbnew
  have hcompare (p : Polarity) : p.orient M.le (denoteIter M hleft) (denoteIter M hl.top) := by
    let rule := UniformityRule.square (ε := ε) (F := .iter) trivial whole diagonal hup
      EffectSystem.iterable_top ha.top hs hbnew hbP hcP (EffectSystem.pure_moves p ⊤)
    apply denoteIter_uniformity M p rule hpre hbnew hleft hl.top
    change denoteIter M hpre = denoteIter M hbnew at hepre
    rw [hepre]
    cases p <;> exact M.toSeqData.le_refl _
  have he : denoteIter M hleft = denoteIter M hl.top := by
    let := M.toSeqData.homOrder
    exact le_antisymm (hcompare .positive) (hcompare .negative)
  exact (denoteIter_coherent M hl hl.top).trans
    (he.symm.trans (heleft.symm.trans (denoteIter_coherent M _ hr)))

end Silmaril.Isotope.Refinement.Models.Denotation
