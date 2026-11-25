module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Bind.Defs

/-! # Pure substitution and straight-line prefixes for mixed request trees -/

@[expose] public section

open Silmaril
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

universe u

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {a c : α}
  {n : Nat} {slots : Fin n → α}

/-- Substitute pure trees for ambient variables under atomic and sum replies. -/
def subst : {n m : Nat} → {slots : Fin n → α} → {target : Fin m → α} →
    Program S T c slots → Sequence.TreeSubst S slots target → Program S T c target
  | _, _, _, _, .ret p, σ => .ret (p.interpret S _ Tree.op σ)
  | _, _, _, _, .atom f args next, σ =>
      .atom f (fun i => (args i).interpret S _ Tree.op σ)
        (subst next (Sequence.liftSubst S σ (S.out f)))
  | _, _, _, _, .sum g args left right, σ =>
      .sum g (fun i => (args i).interpret S _ Tree.op σ)
        (subst left (Sequence.liftSubst S σ (T.left g)))
        (subst right (Sequence.liftSubst S σ (T.right g)))

/-- Insert one ambient slot behind the newest binder. -/
def weakenUnder (x : α) (p : Program S T c (extendSorts a slots)) :
    Program S T c (extendSorts a (extendSorts x slots)) :=
  subst S T p (Sequence.liftAmbientSubst S a x)

/-- Run an atomic sequence before a mixed tree. Substitute the sequence's
pure return into the tree, retaining all observed replies in order. -/
def bindPrefix : {n : Nat} → {slots : Fin n → α} →
    Sequence S a slots → Program S T c (extendSorts a slots) → Program S T c slots
  | _, _, .ret v, q => subst S T q (Sequence.subst0 S v)
  | _, _, .call f args next, q => .atom f args (bindPrefix next (weakenUnder S T (S.out f) q))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed
