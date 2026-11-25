module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Bind.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.InstructionMap.Defs

/-! # Finite raw mixed requests with straight-line prefixes -/

@[expose] public section

open Silmaril
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature SumArgs)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)

abbrev unarySort {g : Ψ} (h : T.arity g = 1) : α :=
  T.arg g ((0 : Fin 1).cast h.symm)

/-- The tuple for a unary sum call after its argument has been bound. -/
def unaryVarArgs {n : Nat} {slots : Fin n → α} {g : Ψ} (h : T.arity g = 1) :
    SumArgs S T (extendSorts (unarySort T h) slots) g :=
  Flatten.argsAtArity S (as := T.arg g) h
    (Fin.cases (motive := fun i => Tree S (extendSorts (unarySort T h) slots) (T.arg g (i.cast h.symm)))
      (.var 0) fun i => i.elim0)

/-- Straight-line computations can return a result or bind an atom for use
in subsequent requests. A sum request can branch recursively. Unary sum
calls also admit a directly nested straight-line argument. -/
inductive Program (c : α) : {n : Nat} → (Fin n → α) → Type (u + 1)
  | straight {n : Nat} {slots : Fin n → α} : Flatten.Program S slots c → Program c slots
  | let1 {n : Nat} {slots : Fin n → α} {a : α} :
      Flatten.Program S slots a → Program c (extendSorts a slots) → Program c slots
  | sum {n : Nat} {slots : Fin n → α} (g : Ψ) :
      SumArgs S T slots g → Program c (extendSorts (T.left g) slots) →
        Program c (extendSorts (T.right g) slots) → Program c slots
  | sumUnary {n : Nat} {slots : Fin n → α} (g : Ψ) (h : T.arity g = 1) :
      Flatten.Program S slots (unarySort T h) →
      Program c (extendSorts (T.left g) slots) →
      Program c (extendSorts (T.right g) slots) → Program c slots

namespace Program

variable {c : α}

def source : {n : Nat} → {slots : Fin n → α} → Program S T c slots → Expr (Φ ⊕ Ψ)
  | _, _, .straight p => p.source.mapInstr Sum.inl
  | _, _, .let1 p q => .let₁ (p.source.mapInstr Sum.inl) (source q)
  | _, _, .sum g args left right =>
      .case (.op (.inr g) (sourceTuple (T.arity g) (fun i => SumCall.treeSource S (args i))))
        (source left) (source right)
  | _, _, .sumUnary g _ p left right =>
      .case (.op (.inr g) (.pair (p.source.mapInstr Sum.inl) .unit))
        (source left) (source right)

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε]

def WellTyped (e : ε) : {n : Nat} → {slots : Fin n → α} → Program S T c slots → Prop
  | _, _, .straight p => Flatten.Program.WellTyped S e p
  | _, _, .let1 p q => Flatten.Program.WellTyped S e p ∧ WellTyped e q
  | _, _, .sum g args left right =>
      (∀ i, DeclaredPure (ε := ε) S (args i)) ∧ instrEff g ≤ e ∧
        WellTyped e left ∧ WellTyped e right
  | _, _, .sumUnary g _ p left right =>
      Flatten.Program.WellTyped S e p ∧ instrEff g ≤ e ∧ WellTyped e left ∧ WellTyped e right

/-- Flatten each straight-line region and move its atomic return through
the remaining tree by typed substitution. -/
noncomputable def compile : {n : Nat} → {slots : Fin n → α} → Program S T c slots → Mixed.Program S T c slots
  | _, _, .straight p => ofSequence S T (Flatten.compile (ε := ε) S p)
  | _, _, .let1 p q => bindPrefix S T (Flatten.compile (ε := ε) S p) (compile q)
  | _, _, .sum g args left right => .sum g args (compile left) (compile right)
  | _, _, .sumUnary g h p left right =>
      bindPrefix S T (Flatten.compile (ε := ε) S p)
        (.sum g (unaryVarArgs S T h) (weakenUnder S T (unarySort T h) (compile left))
          (weakenUnder S T (unarySort T h) (compile right)))

end Program

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw
