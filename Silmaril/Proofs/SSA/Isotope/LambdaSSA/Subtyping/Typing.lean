module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Defs

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Subtyping

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ]
  {Φ : Type v} [HasTy Φ τ]

namespace Exact

/-- Exact SSA typings inject into the proof-relevant system using no coercion.
Because exact typings live in `Prop`, the resulting witness is propositionally
truncated rather than extracted into data. -/
theorem tm_proof {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    (h : LambdaSSA.Tm.HasType Γ t A) : Nonempty (Tm.HasType Γ t A) := by
  induction h with
  | var h => exact ⟨.var h⟩
  | op _ ih => exact ih.elim fun h => ⟨.op h⟩
  | let₁ _ _ iha ihb => exact iha.elim fun ha => ihb.elim fun hb => ⟨.let₁ ha hb⟩
  | pair _ _ iha ihb => exact iha.elim fun ha => ihb.elim fun hb => ⟨.pair ha hb⟩
  | unit => exact ⟨.unit⟩
  | let₂ _ _ iha ihb => exact iha.elim fun ha => ihb.elim fun hb => ⟨.let₂ ha hb⟩
  | inl _ ih => exact ih.elim fun h => ⟨.inl h⟩
  | inr _ ih => exact ih.elim fun h => ⟨.inr h⟩
  | case _ _ _ ihe ihl ihr =>
      exact ihe.elim fun he => ihl.elim fun hl => ihr.elim fun hr => ⟨.case he hl hr⟩
  | abort _ ih => exact ih.elim fun h => ⟨.abort h⟩

theorem region_proof {Γ : VCtx τ} {r : LambdaSSA.Region Φ} {L : LCtx τ}
    (h : LambdaSSA.Region.HasType Γ r L) :
    Nonempty (Region.HasType Γ r L) := by
  induction h with
  | br h ha => exact (tm_proof ha).elim fun ha => ⟨.br h ha⟩
  | case ha _ _ ihl ihr =>
      exact (tm_proof ha).elim fun ha => ihl.elim fun hl => ihr.elim fun hr => ⟨.case ha hl hr⟩
  | let₁ ha _ ihr => exact (tm_proof ha).elim fun ha => ihr.elim fun hr => ⟨.let₁ ha hr⟩
  | let₂ ha _ ihr => exact (tm_proof ha).elim fun ha => ihr.elim fun hr => ⟨.let₂ ha hr⟩
  | cfg R _ _ ihe ihb =>
      exact ihe.elim fun he =>
        ⟨.cfg R he (fun i => Classical.choice (ihb i))⟩

end Exact

end Silmaril.Isotope.LambdaSSA.Subtyping
