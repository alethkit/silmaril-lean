module

public import Silmaril.Raw.SSA.Isotope.Morphism.CaseSSASemantics
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.OperationalDenotation
public import Silmaril.Raw.SSA.Isotope.Morphism.SeqCase.Monadic
public import Silmaril.Raw.SSA.Isotope.Morphism.Instructions.LetCase
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.InstructionMap

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

/-- Relabelling instructions commutes with positional expression erasure. -/
theorem erase_mapInstr {Φ : Type u} {Ψ : Type v} {n : Nat}
    (f : Φ → Ψ) (t : LetCase.LocallyNameless.Tm Empty Φ n) :
    erase (t.mapInstr f) = (erase t).mapInstr f := by
  induction t with
  | fv x => exact x.elim
  | _ => simp_all [erase, LetCase.LocallyNameless.Tm.mapInstr, LambdaSSA.Tm.mapInstr]

end Silmaril.Isotope.Morphism.CaseSSA
