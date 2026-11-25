module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.InstructionMap.Defs

/-! # One sum-returning request with raw straight-line arms -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature SumArgs)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.RawArms

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {n : Nat} {slots : Fin n → α} {c : α}

/-- The selected atomic payload and the ambient variables are available to
each arm of the single sum call. The arms may have nested effectful arguments. -/
structure Program (slots : Fin n → α) (c : α) where
  op : Ψ
  args : SumArgs S T slots op
  left : Flatten.Program S (extendSorts (T.left op) slots) c
  right : Flatten.Program S (extendSorts (T.right op) slots) c

namespace Program

/-- Render the unflattened arms under their corresponding payload binders. -/
def source (p : Program S T slots c) : Expr (Φ ⊕ Ψ) :=
  .case (.op (.inr p.op) (sourceTuple (T.arity p.op) (fun i => SumCall.treeSource S (p.args i))))
    (p.left.source.mapInstr Sum.inl) (p.right.source.mapInstr Sum.inl)

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε]

def WellTyped (e : ε) (p : Program S T slots c) : Prop :=
  (∀ i, DeclaredPure (ε := ε) S (p.args i)) ∧ instrEff p.op ≤ e ∧
    Flatten.Program.WellTyped S e p.left ∧ Flatten.Program.WellTyped S e p.right

/-- Normalize each arm in its own payload context. The sum request remains
the single outer request. -/
noncomputable def compile (p : Program S T slots c) : Mixed.Program S T c slots :=
  .sum p.op p.args
    (Mixed.ofSequence S T (Flatten.compile (ε := ε) S p.left))
    (Mixed.ofSequence S T (Flatten.compile (ε := ε) S p.right))

end Program

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.RawArms
