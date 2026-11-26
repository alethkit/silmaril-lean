module

public import Silmaril.Raw.SSA.Isotope.Morphism.CaseSSASemantics
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.OperationalDenotation
public import Silmaril.Raw.SSA.Isotope.Morphism.SeqCase.Monadic

/-! # LetCase expression erasure and the checked let-family model interfaces -/

public section

universe u v w

namespace Silmaril.Isotope.Morphism.CaseSSA

/-- Positional expression erasure preserves and reflects the native LetCase
finite evaluation judgment. -/
theorem erase_caseEval_iff {α : Type u} {Φ : Type v} {σ : Type w} {n : Nat}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : LambdaSSA.Semantics.Env α} {bound : LetCase.Semantics.BoundEnv α n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} {s s' : σ} {value : Value α}
    (agree : EnvAgrees env bound) :
    LambdaSSA.Semantics.Tm.Eval instr env (erase t) s value s' ↔
      LetCase.Semantics.Eval instr Empty.elim bound t s value s' :=
  (erase_eval_iff agree).trans CaseIter.embed_eval_iff

end Silmaril.Isotope.Morphism.CaseSSA
