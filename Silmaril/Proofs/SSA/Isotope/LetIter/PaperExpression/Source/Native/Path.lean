module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Path.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Reflection.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag.Native.Thms
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.PathProofs

open LocallyNameless (Tm HasTypeEffect AbortEquiv Equiv Refinement)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx τ ε} {A X Y : τ} {e : ε} {a b : PathTerm Φ Γ A e}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "β" => Γ.toBoundCtx

omit [TypeFormers τ] [EffectIteration ε] in
private theorem pure_cons (hp : Γ.Pure) (D : τ) : EffectCtx.Pure ((D, ⊥) :: Γ) :=
  fun i => Fin.cases rfl hp i

theorem reflects (h : RestrictedPath e Γ A a b) (hp : Γ.Pure) :
    Eqv Γ A e a.source.val b.source.val := by
  induction h with
  | refl a => exact .refl a.source.prop
  | source h => exact .step h
  | @core _ _ a b h => exact eqv_of_coreAxiom_toLetIter hp a.source b.source a.lowered b.lowered h
  | @abortSequence _ _ a b h => exact eqv_of_abortSequence_toLetIter a.source b.source a.lowered b.lowered h
  | symm _ ih => exact (ih hp).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ hp).trans (ih₂ hp)
  | left _ p _ _ _ ih => exact .let1 (.refl p.source.prop) (ih (pure_cons hp _))
  | right _ p _ _ _ ih => exact .let1 (.refl p.source.prop) (ih (pure_cons hp _))

private theorem term_typed (a : PathTerm Φ Γ A e) : HasTypeEffect Γ₀ β a.term A e := by
  obtain ⟨_, a', ht⟩ := a.source.prop.toLetIter
  exact Option.some.inj (a'.symm.trans a.lowered) ▸ ht

theorem left_native (g : PathTerm Φ Γ (coprod X Y) e) (p : PathTerm Φ Γ X e)
    (tag : KnownTag Γ X Y e g.source.val (.inl p.source.val))
    {l l' : PathTerm Φ ((X, ⊥) :: Γ) A e} {r r' : Tm Empty Φ (Γ.length + 1)}
    (hl : AbortEquiv (⊥ : ε) Γ₀ (.snoc β X) l.term l'.term A)
    (hr : AbortEquiv (⊥ : ε) Γ₀ (.snoc β Y) r r' A) :
    AbortEquiv (⊥ : ε) Γ₀ β (p.let1 l).term (.case g.term l.term r) A ∧
    AbortEquiv (⊥ : ε) Γ₀ β (.case g.term l.term r)
      (.let₁ g.term (.case (.bv 0) l'.term.underBinder r'.underBinder)) A ∧
    AbortEquiv (⊥ : ε) Γ₀ β (.let₁ g.term (.case (.bv 0) l'.term.underBinder r'.underBinder))
      (p.let1 l').term A := by
  have h₁ := tag.native_inl g.lowered p.lowered (term_typed l) hr.hasType.1
  have h₂ := tag.native_inl g.lowered p.lowered (term_typed l') hr.hasType.2
  have hguard := (term_typed g).1
  exact ⟨h₁.2.1.symm,
    (Refinement.case (Refinement.refl hguard) hl hr).trans
      (.equiv (Equiv.bindCase hguard hl.hasType.2 hr.hasType.2)),
    h₂.2.2⟩

theorem right_native (g : PathTerm Φ Γ (coprod X Y) e) (p : PathTerm Φ Γ Y e)
    (tag : KnownTag Γ X Y e g.source.val (.inr p.source.val))
    {l l' : Tm Empty Φ (Γ.length + 1)} {r r' : PathTerm Φ ((Y, ⊥) :: Γ) A e}
    (hl : AbortEquiv (⊥ : ε) Γ₀ (.snoc β X) l l' A)
    (hr : AbortEquiv (⊥ : ε) Γ₀ (.snoc β Y) r.term r'.term A) :
    AbortEquiv (⊥ : ε) Γ₀ β (p.let1 r).term (.case g.term l r.term) A ∧
    AbortEquiv (⊥ : ε) Γ₀ β (.case g.term l r.term)
      (.let₁ g.term (.case (.bv 0) l'.underBinder r'.term.underBinder)) A ∧
    AbortEquiv (⊥ : ε) Γ₀ β (.let₁ g.term (.case (.bv 0) l'.underBinder r'.term.underBinder))
      (p.let1 r').term A := by
  have h₁ := tag.native_inr g.lowered p.lowered hl.hasType.1 (term_typed r)
  have h₂ := tag.native_inr g.lowered p.lowered hl.hasType.2 (term_typed r')
  have hguard := (term_typed g).1
  exact ⟨h₁.2.1.symm,
    (Refinement.case (Refinement.refl hguard) hl hr).trans
      (.equiv (Equiv.bindCase hguard hl.hasType.2 hr.hasType.2)),
    h₂.2.2⟩

theorem toNative (h : RestrictedPath e Γ A a b) :
    AbortEquiv (⊥ : ε) Γ₀ β a.term b.term A := by
  induction h with
  | refl a => exact Refinement.refl (term_typed a).1
  | @source _ _ a b h => exact (Eqv.step h).toLetIter a.lowered b.lowered
  | @core _ _ a b h => exact .equiv (.ax h (term_typed a).1 (term_typed b).1)
  | @abortSequence _ _ a b h => exact .primitive h (term_typed a).1 (term_typed b).1
  | symm _ ih => exact AbortEquiv.symm ih
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | left g p tag _ hr ih =>
    obtain ⟨entry, middle, exit⟩ := left_native g p tag ih hr
    exact entry.trans (middle.trans exit)
  | right g p tag hl _ ih =>
    obtain ⟨entry, middle, exit⟩ := right_native g p tag hl ih
    exact entry.trans (middle.trans exit)

end Silmaril.Isotope.LetIter.PaperExpression.Source.PathProofs
