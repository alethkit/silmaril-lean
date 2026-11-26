module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Thms

/-! # Free pure values for primitive inputs of arbitrary structured type -/

@[expose] public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation)
open Silmaril.Isotope.Semantics (BoundEnv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)]
  {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- The pure operations may return an atom or unit. The inputs may have
any discrete type, including nested sums, products and empty. -/
inductive PureResult (B : Ty α) : Type u
  | atom (a : α) (type : B = .base a)
  | unit (type : B = .unit)

/-- Only bottom-pure primitives are restricted by the pure profile. -/
abbrev Profile (Φ : Type u) [HasTy Φ (Ty α)] (ε : Type r) [HasEff Φ ε] [Bot ε] :=
  ∀ f : Φ, IsPure (⊥ : ε) f → PureResult (instrTrg f : Ty α)

/-- Pure constructor values over an atomic context. A pure atomic primitive
is a free generator indexed by its original symbol and full typed argument. -/
inductive Value {n : Nat} (slots : Fin n → α) : Ty α → Type u
  | var (i : Fin n) : Value slots (.base (slots i))
  | op (f : Φ) (pure : IsPure (⊥ : ε) f) {a : α}
      (type : (instrTrg f : Ty α) = .base a) (arg : Value slots (instrSrc f)) : Value slots (.base a)
  | unit : Value slots .unit
  | pair {A B : Ty α} : Value slots A → Value slots B → Value slots (.product A B)
  | inl {A B : Ty α} : Value slots A → Value slots (.coprod A B)
  | inr {A B : Ty α} : Value slots B → Value slots (.coprod A B)

/-- The written constructor fragment. Bottom typing supplies purity of
its primitive applications, including those whose result is unit. -/
inductive ConstructorLeaf : Expr Φ → Prop
  | var (i : Nat) : ConstructorLeaf (.var i)
  | unit : ConstructorLeaf .unit
  | op {f : Φ} {arg : Expr Φ} : ConstructorLeaf arg → ConstructorLeaf (.op f arg)
  | pair {a b : Expr Φ} : ConstructorLeaf a → ConstructorLeaf b → ConstructorLeaf (.pair a b)
  | inl {a : Expr Φ} : ConstructorLeaf a → ConstructorLeaf (.inl a)
  | inr {b : Expr Φ} : ConstructorLeaf b → ConstructorLeaf (.inr b)

variable {n : Nat} {slots : Fin n → α}

abbrev Atom (slots : Fin n → α) (a : α) := Value (Φ := Φ) (ε := ε) slots (.base a)

namespace Value

/-- Pack a constructor value into the ordinary interpretation of the type.
At atoms, the value algebra is the free generator syntax itself. -/
def encode : {A : Ty α} → Value (Φ := Φ) (ε := ε) slots A → Ty.denote (Atom (Φ := Φ) (ε := ε) slots) A
  | .base _, v => v
  | .unit, .unit => PUnit.unit
  | .empty, v => nomatch v
  | .product _ _, .pair p q => (p.encode, q.encode)
  | .coprod _ _, .inl p => Sum.inl p.encode
  | .coprod _ _, .inr q => Sum.inr q.encode

/-- Decode all the product fields and injection tags of a semantic input. -/
def decode : (A : Ty α) → Ty.denote (Atom (Φ := Φ) (ε := ε) slots) A → Value (Φ := Φ) (ε := ε) slots A
  | .base _, v => v
  | .unit, _ => .unit
  | .empty, v => v.elim
  | .product A B, v => .pair (decode A v.1) (decode B v.2)
  | .coprod A _, Sum.inl p => .inl (decode A p)
  | .coprod _ B, Sum.inr q => .inr (decode B q)

/-- Evaluate the variables of a free value as atoms over another sorted context.
Applied primitives and every constructor retain their original types. -/
def subst {m : Nat} {modelSlots : Fin m → α}
    (vars : (i : Fin n) → Atom (Φ := Φ) (ε := ε) modelSlots (slots i)) :
    {A : Ty α} → Value (Φ := Φ) (ε := ε) slots A → Value (Φ := Φ) (ε := ε) modelSlots A
  | _, .var i => vars i
  | _, .op f hf ht arg => .op f hf ht (arg.subst vars)
  | _, .unit => .unit
  | _, .pair p q => .pair (p.subst vars) (q.subst vars)
  | _, .inl p => .inl (p.subst vars)
  | _, .inr p => .inr (p.subst vars)

def source : {A : Ty α} → Value (Φ := Φ) (ε := ε) slots A → Expr Φ
  | _, .var i => .var i
  | _, .op f _ _ arg => .op f arg.source
  | _, .unit => .unit
  | _, .pair p q => .pair p.source q.source
  | _, .inl p => .inl p.source
  | _, .inr q => .inr q.source

@[reducible] def native : {A : Ty α} → Value (Φ := Φ) (ε := ε) slots A → Tm Empty Φ n
  | _, .var i => .bv i
  | _, .op f _ _ arg => .op f arg.native
  | _, .unit => .unit
  | _, .pair p q => .pair p.native q.native
  | _, .inl p => .inl p.native
  | _, .inr q => .inr q.native

/-- Type a rendered value in a context with the matching atomic slots. -/
def derivation {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (slots i)) :
    {A : Ty α} → (v : Value (Φ := Φ) (ε := ε) slots A) →
      Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β v.native A
  | _, .var i => cast (congrArg (Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β (.bv i)) (hs i))
      (Derivation.bv (ι := i))
  | _, .op f _ h arg => cast (congrArg (Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β (.op f arg.native)) h)
      (.op (arg.derivation hs))
  | _, .unit => .unit
  | _, .pair p q => .pair (p.derivation hs) (q.derivation hs)
  | _, .inl p => .inl (p.derivation hs)
  | _, .inr q => .inr (q.derivation hs)

end Value

variable (slots)

/-- The canonical pure maps interpret each atomic-result primitive as its
free generator and each unit-result primitive as the unique unit value. -/
def pureMaps (profile : Profile (α := α) Φ ε) :
    Structured.PureMaps (Φ := Φ) (ε := ε) (Atom (Φ := Φ) (ε := ε) slots) :=
  fun f hf arg =>
    match profile f hf with
    | .atom a h =>
        cast (congrArg (Ty.denote (Atom (Φ := Φ) (ε := ε) slots)) h.symm) (Value.op f hf (a := a) h (Value.decode _ arg))
    | .unit h => cast (congrArg (Ty.denote (Atom (Φ := Φ) (ε := ε) slots)) h.symm) PUnit.unit

/-- Install arbitrary sorted free atoms in the matching native slots. -/
def valuationEnv {m : Nat} (modelSlots : Fin m → α)
    {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (slots i))
    (vars : (i : Fin n) → Atom (Φ := Φ) (ε := ε) modelSlots (slots i)) :
    BoundEnv (Ty.denote (Lifted (Atom (Φ := Φ) (ε := ε) modelSlots))) β :=
  fun i => cast (congrArg (Ty.denote (Lifted (Atom (Φ := Φ) (ε := ε) modelSlots))) (hs i).symm) ⟨vars i⟩

/-- The canonical valuation uses a distinct free generator for each slot. -/
def variableEnv {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (slots i)) :
    BoundEnv (Ty.denote (Lifted (Atom (Φ := Φ) (ε := ε) slots))) β :=
  valuationEnv slots slots hs Value.var

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues
