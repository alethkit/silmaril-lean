module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Defs

/-! # A response-bearing sum instruction followed by straight-line arms -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.Semantics Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall

universe u v r

/-- The additional instructions take atomic tuples and return one of two
atomic payloads. The ordinary signature supplies all atomic operations. -/
structure SumSignature (α Ψ : Type u) where
  arity : Ψ → Nat
  arg : (g : Ψ) → Fin (arity g) → α
  left : Ψ → α
  right : Ψ → α

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)

abbrev result (g : Ψ) : Ty α := .coprod (.base (T.left g)) (.base (T.right g))

@[instance_reducible] def endpoints : HasTy (Φ ⊕ Ψ) (Ty α) :=
  ⟨Sum.elim (fun f => input (S.arity f) (S.arg f))
      (fun g => input (T.arity g) (T.arg g)),
    Sum.elim (fun f => .base (S.out f)) (result T)⟩

@[instance_reducible] def effects {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] :
    HasEff (Φ ⊕ Ψ) ε :=
  ⟨Sum.elim instrEff instrEff⟩

variable {n : Nat} (slots : Fin n → α)

abbrev SumArgs (g : Ψ) := (i : Fin (T.arity g)) → Tree S slots (T.arg g i)
abbrev SumRequest := (g : Ψ) × SumArgs S T slots g
abbrev SumResponse (g : Ψ) := Tree S slots (T.left g) ⊕ Tree S slots (T.right g)

inductive Event : Type (u + 1) → Type (u + 1)
  | atom (f : Φ) (args : Args S slots f) : Event (Tree S slots (S.out f))
  | sum (g : Ψ) (args : SumArgs S T slots g) : Event (SumResponse S T slots g)

def atomLabel {X : Type (u + 1)} : Event S T slots X → Option (Request S slots)
  | .atom f args => some ⟨f, args⟩
  | .sum _ _ => none

def sumLabel {X : Type (u + 1)} : Event S T slots X → Option (SumRequest S T slots)
  | .atom _ _ => none
  | .sum g args => some ⟨g, args⟩

/-- Recover the symbol and full sorted arguments of a visible request.
A returned value has no request label. -/
noncomputable def headRequest {B : Type v} (t : ITree.Tree (Event S T slots) B) :
    _root_.Part (Option (Request S slots ⊕ SumRequest S T slots)) :=
  (ITree.out t).map (fun
    | .ret _ => none
    | .vis (.atom f args) _ => some (.inl ⟨f, args⟩)
    | .vis (.sum g args) _ => some (.inr ⟨g, args⟩))

/-- A sum response retains its constructor and its sorted payload. -/
def responseValue {g : Ψ} (r : SumResponse S T slots g) :
    Ty.denote (Atom S slots) (result T g) :=
  r.elim (fun a => Sum.inl ⟨a⟩) (fun b => Sum.inr ⟨b⟩)

noncomputable def instructions {ε : Type r} [HasEff Φ ε] [Bot ε] :
    @InstructionModel (Ty α) (Ty.denote (Atom S slots)) (Φ ⊕ Ψ)
      (ITree.Tree (Event S T slots)) (endpoints S T) := by
  classical
  let instr := endpoints S T
  exact ⟨fun
    | .inl f, x => if IsPure (⊥ : ε) f then
        ITree.ret ⟨Tree.op f (readArgs S slots f x)⟩
      else ITree.vis (.atom f (readArgs S slots f x)) (fun r => ITree.ret ⟨r⟩)
    | .inr g, x => ITree.vis (.sum g (unpackArgs S slots (T.arity g) (T.arg g) x))
        (fun r => ITree.ret (responseValue S T slots r))⟩

variable {slots}

/-- Render an ordinary pure tree into the extended instruction signature. -/
def treeSource : {a : α} → Tree S slots a → Expr (Φ ⊕ Ψ)
  | _, .var i => .var i.val
  | _, .op f args => .op (.inl f) (sourceTuple (S.arity f) (fun i => treeSource (args i)))

def treeNative : {a : α} → Tree S slots a → Tm Empty (Φ ⊕ Ψ) n
  | _, .var i => .bv i
  | _, .op f args => .op (.inl f) (nativeTuple (S.arity f) (fun i => treeNative (args i)))

variable {c : α}

/-- The arm sequences retain only the selected payload and the ambient slots. -/
def armSource : {n : Nat} → {slots : Fin n → α} → Sequence S c slots → Expr (Φ ⊕ Ψ)
  | _, _, .ret p => treeSource (Ψ := Ψ) S p
  | _, _, .call f args next =>
      .let₁ (.op (.inl f) (sourceTuple (S.arity f) (fun i => treeSource S (args i))))
        (armSource next)

def armNative : {n : Nat} → {slots : Fin n → α} → Sequence S c slots → Tm Empty (Φ ⊕ Ψ) n
  | _, _, .ret p => treeNative (Ψ := Ψ) S p
  | _, _, .call f args next =>
      .let₁ (.op (.inl f) (nativeTuple (S.arity f) (fun i => treeNative S (args i))))
        (armNative next)

/-- One visible request is the scrutinee of a case. The arms are normalized
straight-line programs indexed by the two response payload sorts. -/
structure Program (slots : Fin n → α) (c : α) where
  op : Ψ
  args : SumArgs S T slots op
  left : Sequence S c (extendSorts (T.left op) slots)
  right : Sequence S c (extendSorts (T.right op) slots)

namespace Program

def source (p : Program S T slots c) : Expr (Φ ⊕ Ψ) :=
  .case (.op (.inr p.op) (sourceTuple (T.arity p.op) (fun i => treeSource S (p.args i))))
    (armSource S p.left) (armSource S p.right)

def native (p : Program S T slots c) : Tm Empty (Φ ⊕ Ψ) n :=
  .case (.op (.inr p.op) (nativeTuple (T.arity p.op) (fun i => treeNative S (p.args i))))
    (armNative S p.left) (armNative S p.right)

def WellTyped {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε]
    (e : ε) (p : Program S T slots c) : Prop :=
  (∀ i, DeclaredPure (ε := ε) S (p.args i)) ∧ instrEff p.op ≤ e ∧
    Sequence.WellTyped S e p.left ∧ Sequence.WellTyped S e p.right

variable {m : Nat} (modelSlots : Fin m → α)

/-- The outer call is one visible node. Its selected continuation starts with
the corresponding straight-line arm at the payload-extended valuation. -/
noncomputable def denote (p : Program S T slots c)
    (vars : (i : Fin n) → Tree S modelSlots (slots i)) :
    ITree.Tree (Event S T modelSlots) (Atom S modelSlots c) :=
  ITree.vis (.sum p.op (fun i => (p.args i).interpret S (Tree S modelSlots) Tree.op vars))
    (fun
      | .inl r => Sequence.denoteWith S modelSlots Event.atom p.left (extendValues S modelSlots r vars)
      | .inr r => Sequence.denoteWith S modelSlots Event.atom p.right (extendValues S modelSlots r vars))

end Program

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
