module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Thms

/-! # Source reflection for matched decision trees -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Proofs

universe u w

variable {α Φ : Type u} (S : Signature α Φ) {ε : Type w}
  [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {shape : Shape Γ} {c : α}

public theorem source_wf (hΓ : Γ.Pure) (e : ε)
    (p : Program S c shape) (hp : Program.WellTyped S e p) :
    letI := S.endpoints
    Wf Γ p.source (.base c) e := by
  let instr := S.endpoints
  induction p with
  | @leaf Γ slots hs leaf =>
    exact Flatten.source_wf S hΓ hs e leaf hp
  | @split Γ i x y ht left right l r ihl ihr =>
    exact SumSplit.caseArms_wf i ht (hΓ i)
      (ihl (SumSplit.branchCtx_pure hΓ i (.base x)) hp.1)
      (ihr (SumSplit.branchCtx_pure hΓ i (.base y)) hp.2)

variable [EffectIteration ε] [DecidableEq α]

omit [DecidableEq α] in
private theorem transport_arms {Δ : EffectCtx (Ty α) ε} {e : ε}
    {a b a' b' : Expr Φ} {t s t' s' : Tm Empty Φ Δ.length}
    (hpa : letI := S.endpoints; Eqv Δ (.base c) e a a')
    (hpb : letI := S.endpoints; Eqv Δ (.base c) e b b')
    (ht : a.toLetIter Δ.length = some t) (hs : b.toLetIter Δ.length = some s)
    (ht' : a'.toLetIter Δ.length = some t') (hs' : b'.toLetIter Δ.length = some s')
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Δ.toBoundCtx t s (.base c)) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Δ.toBoundCtx t' s' (.base c) := by
  let instr := S.endpoints
  exact (hpa.toLetIter ht ht').symm.trans (hn.trans (hpb.toLetIter hs hs'))

private theorem eqv_of_native_aux (e : ε) (shape : Shape Γ) :
    letI := S.endpoints
    ∀ (p q : Program S c shape), Γ.Pure → Program.WellTyped S e p → Program.WellTyped S e q →
      ∀ {t s : Tm Empty Φ Γ.length},
        p.source.toLetIter Γ.length = some t → q.source.toLetIter Γ.length = some s →
        AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base c) →
        Eqv Γ (.base c) e p.source q.source := by
  let instr := S.endpoints
  induction shape with
  | @leaf Γ slots hs =>
    intro p q hΓ hp hq t s ht hs' hn
    cases p with
    | leaf p =>
      cases q with
      | leaf q =>
        exact (Flatten.endpoint_reflection S hΓ hs e p q hp hq ht hs').mp hn
  | @split Γ i x y hi sl sr ihl ihr =>
    intro p q hΓ hp hq t s ht hs hn
    cases p with
    | split _ l r =>
      cases q with
      | split _ l' r' =>
        let ΔL := SumSplit.branchCtx Γ i (.base x)
        let ΔR := SumSplit.branchCtx Γ i (.base y)
        have hΔL : EffectCtx.Pure ΔL := SumSplit.branchCtx_pure hΓ i (.base x)
        have hΔR : EffectCtx.Pure ΔR := SumSplit.branchCtx_pure hΓ i (.base y)
        have hwl := source_wf S hΔL e l hp.1
        have hwr := source_wf S hΔR e r hp.2
        have hwl' := source_wf S hΔL e l' hq.1
        have hwr' := source_wf S hΔR e r' hq.2
        obtain ⟨_, ll, _⟩ := hwl.toLetIter
        obtain ⟨_, lr, _⟩ := hwr.toLetIter
        obtain ⟨_, ll', _⟩ := hwl'.toLetIter
        obtain ⟨_, lr', _⟩ := hwr'.toLetIter
        have hcase := SumSplit.native_specializations i hΓ hi ht hs hn
        obtain ⟨⟨_, _, htl, hsl, hnL⟩, ⟨_, _, htr, hsr, hnR⟩⟩ := hcase
        have hL := transport_arms S
          (SumSplit.caseArms_left i hi (hΓ i) hwl hwr)
          (SumSplit.caseArms_left i hi (hΓ i) hwl' hwr') htl hsl ll ll' hnL
        have hR := transport_arms S
          (SumSplit.caseArms_right i hi (hΓ i) hwl hwr)
          (SumSplit.caseArms_right i hi (hΓ i) hwl' hwr') htr hsr lr lr' hnR
        exact (SumSplit.caseArms_eqv_iff i hi (hΓ i) hwl hwr hwl' hwr').mpr
          ⟨ihl l l' hΔL hp.1 hq.1 ll ll' hL, ihr r r' hΔR hp.2 hq.2 lr lr' hR⟩

public theorem endpoint_reflection (hΓ : Γ.Pure) (e : ε)
    (p q : Program S c shape) (hp : Program.WellTyped S e p) (hq : Program.WellTyped S e q)
    {t s : Tm Empty Φ Γ.length}
    (ht : p.source.toLetIter Γ.length = some t) (hs : q.source.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base c) ↔
      Eqv Γ (.base c) e p.source q.source := by
  let instr := S.endpoints
  exact ⟨eqv_of_native_aux S e shape p q hΓ hp hq ht hs, fun h => h.toLetIter ht hs⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Proofs
