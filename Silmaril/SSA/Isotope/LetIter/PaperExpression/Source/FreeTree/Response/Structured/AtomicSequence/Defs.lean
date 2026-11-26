module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues.Thms

/-! # Finite source sequences of visible calls with atomic replies -/

@[expose] public section

open Silmaril.Isotope Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- A sequence returns a pure constructor value or binds the atomic reply of
a visible request and proceeds in the extended scope. The arguments retain
their original structured input types. -/
inductive Program (A : Ty α) : {n : Nat} → (Fin n → α) → Type u
  | ret {n : Nat} {slots : Fin n → α} : Value (Φ := Φ) (ε := ε) slots A → Program A slots
  | call {n : Nat} {slots : Fin n → α} (f : Φ) (visible : ¬ IsPure (⊥ : ε) f)
      {a : α} (reply : (instrTrg f : Ty α) = .base a) (arg : Value (Φ := Φ) (ε := ε) slots (instrSrc f))
      (next : Program A (Fin.cases a slots)) : Program A slots

theorem replySlots {n : Nat} {slots : Fin n → α} {β : BoundCtx (Ty α) n}
    (hs : ∀ i, β.get i = .base (slots i)) {R : Ty α} {a : α} (reply : R = .base a) :
    ∀ i : Fin (n + 1), (β.snoc R).get i = .base (Fin.cases a slots i) :=
  Fin.cases (motive := fun i => (β.snoc R).get i = .base (Fin.cases a slots i)) reply hs

namespace Program

variable {A : Ty α}

def source : {n : Nat} → {slots : Fin n → α} → Program (Φ := Φ) (ε := ε) A slots → Expr Φ
  | _, _, .ret value => value.source
  | _, _, .call f _ _ arg next => .let₁ (.op f arg.source) next.source

@[reducible] def native : {n : Nat} → {slots : Fin n → α} → Program (Φ := Φ) (ε := ε) A slots → Tm Empty Φ n
  | _, _, .ret value => value.native
  | _, _, .call f _ _ arg next => .let₁ (.op f arg.native) next.native

/-- Compile a sequence to exact native typing in a matching atomic environment. -/
def derivation : {n : Nat} → {slots : Fin n → α} → {β : BoundCtx (Ty α) n} →
    (p : Program (Φ := Φ) (ε := ε) A slots) → (∀ i, β.get i = .base (slots i)) →
      Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β p.native A
  | _, _, _, .ret value, hs => value.derivation hs
  | _, _, _, .call _ _ h arg next, hs => .let₁ (.op (arg.derivation hs)) (next.derivation (replySlots hs h))

/-- Run the exact native derivation under a sorted valuation in any of the
free-value models, including one with fresh generators for subsequent replies. -/
noncomputable def denote {n m : Nat} {slots : Fin n → α} {β : BoundCtx (Ty α) n}
    (p : Program (Φ := Φ) (ε := ε) A slots) (profile : Profile (α := α) Φ ε)
    (modelSlots : Fin m → α) (hs : ∀ i, β.get i = .base (slots i))
    (vars : (i : Fin n) → Atom (Φ := Φ) (ε := ε) modelSlots (slots i)) :
    ITree.Tree (Event (Φ := Φ) (Atom (Φ := Φ) (ε := ε) modelSlots))
      (Ty.denote (Lifted (Atom (Φ := Φ) (ε := ε) modelSlots)) A) :=
  let V := Atom (Φ := Φ) (ε := ε) modelSlots
  (p.derivation hs).denote (Ty.denote (Lifted V)) (instructions V (pureMaps modelSlots profile))
    (fun x => x.elim) (valuationEnv slots modelSlots hs vars)

variable [Preorder ε]

/-- Every visible call must be admitted at the same original upper bound. -/
def Within (e : ε) : {n : Nat} → {slots : Fin n → α} → Program (Φ := Φ) (ε := ε) A slots → Prop
  | _, _, .ret _ => True
  | _, _, .call f _ _ _ next => instrEff f ≤ e ∧ next.Within e

end Program
section Written

variable [Preorder ε]

/-- Written finite call sequences with constructor arguments and constructor
returns. Typing and the common bound are recorded before normalization. -/
inductive Written (A : Ty α) (e : ε) : EffectCtx (Ty α) ε → Expr Φ → Prop
  | ret {Γ : EffectCtx (Ty α) ε} {a : Expr Φ}
      (typed : Wf Γ a A (⊥ : ε)) (leaf : ConstructorLeaf a) : Written A e Γ a
  | call {Γ : EffectCtx (Ty α) ε} {arg k : Expr Φ} {f : Φ} {a : α}
      (visible : ¬ IsPure (⊥ : ε) f) (reply : (instrTrg f : Ty α) = .base a)
      (typed : Wf Γ arg (instrSrc f) (⊥ : ε)) (leaf : ConstructorLeaf arg)
      (bound : instrEff f ≤ e) (next : Written A e ((instrTrg f, ⊥) :: Γ) k) :
      Written A e Γ (.let₁ (.op f arg) k)

end Written

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence
