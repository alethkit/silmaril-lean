module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Result.Defs

/-! # Native and weak-tree interpretations of typed constructor returns -/

@[expose] public section

open Silmaril Silmaril.Isotope Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization (Value)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature treeNative)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written

universe u

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {A : Ty α} {n m : Nat} {ss : Fin n → α} (modelSlots : Fin m → α)

/-- Interpret the atomic leaves in the free value algebra, keeping products,
unit and the injection tag in the returned value. -/
def valueDenote (vars : (i : Fin n) → Tree S modelSlots (ss i)) (v : Value S ss A) :
    Ty.denote (Atom S modelSlots) A :=
  v.denoteWith S (fun t => ⟨t.interpret S (Tree S modelSlots) Tree.op vars⟩)

def valueNative : {A : Ty α} → Value S ss A → Tm Empty (Φ ⊕ Ψ) n
  | _, .tree t => treeNative S t
  | _, .unit => .unit
  | _, .pair p q => .pair (valueNative p) (valueNative q)
  | _, .inl p => .inl (valueNative p)
  | _, .inr q => .inr (valueNative q)

def Code.native : {n : Nat} → {ss : Fin n → α} → Code S T A ss → Tm Empty (Φ ⊕ Ψ) n
  | _, _, .ret v => valueNative S v
  | _, _, .atom f args next =>
      .let₁ (.op (.inl f) (nativeTuple (S.arity f) (fun i => treeNative S (args i)))) (native next)
  | _, _, .sum g args left right =>
      .case (.op (.inr g) (nativeTuple (T.arity g) (fun i => treeNative S (args i))))
        (native left) (native right)

/-- Requests retain their original symbols, arguments and replies. Only the
return carrier depends on the possibly structured result type. -/
noncomputable def Code.denote : {n : Nat} → {ss : Fin n → α} → Code S T A ss →
    ((i : Fin n) → Tree S modelSlots (ss i)) →
      ITree.Tree (SumCall.Event S T modelSlots) (Ty.denote (Atom S modelSlots) A)
  | _, _, .ret v, vars => ITree.ret (valueDenote S modelSlots vars v)
  | _, _, .atom f args next, vars =>
      ITree.vis (.atom f (fun i => (args i).interpret S (Tree S modelSlots) Tree.op vars))
        (fun r => denote next (extendValues S modelSlots r vars))
  | _, _, .sum g args left right, vars =>
      ITree.vis (.sum g (fun i => (args i).interpret S (Tree S modelSlots) Tree.op vars))
        (fun
          | .inl r => denote left (extendValues S modelSlots r vars)
          | .inr r => denote right (extendValues S modelSlots r vars))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written
