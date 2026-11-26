module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reconstruction.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Defs

/-! # Exact derivations for reply-shape substitutions -/

@[expose] public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation DerivSubst)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape

universe u v w

variable {α : Type u} {Φ : Type v} {ε : Type w} [Bot ε] {n : Nat}
  {sorts : Fin n → α} {Γ : EffectCtx (Ty α) ε} {R : Ty α}

theorem get_fieldType (i : Fin n) :
    (fieldCtx sorts Γ).toBoundCtx.get (fieldIndex sorts Γ i) = .base (sorts i) :=
  (EffectCtx.get_toBoundCtx _ _).trans (congrArg Prod.fst (get_fieldIndex i))

theorem get_ambientType (i : Fin Γ.length) :
    (fieldCtx sorts Γ).toBoundCtx.get (ambientIndex sorts Γ i) = Γ.toBoundCtx.get i :=
  (EffectCtx.get_toBoundCtx _ _).trans
    ((congrArg Prod.fst (get_ambientIndex i)).trans (EffectCtx.get_toBoundCtx _ _).symm)

/-- Compile the constructor substitution to exact native derivations. -/
def specializeDerivSubst [HasTy Φ (Ty α)] (shape : ReplyShape sorts R) (Γ : EffectCtx (Ty α) ε) :
    DerivSubst (Γ := Ctx.nil (ν := Empty)) (Γ.toBoundCtx.snoc R) (fieldCtx sorts Γ).toBoundCtx
      (shape.nativeSubst (Φ := Φ) Γ) :=
  Fin.cases (shape.derivation (fieldIndex sorts Γ) get_fieldType)
    (fun i => (get_ambientType i) ▸ .bv)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape
