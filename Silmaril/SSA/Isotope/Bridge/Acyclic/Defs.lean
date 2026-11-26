module

public import Silmaril.SSA.Isotope.Bridge.CaseSSA.Thms

/-! # Single-exit, structured acyclic λSSA

A region returns one typed payload. A join's entry transfers to one local
block. The block receives that payload and the values in scope at the join.
The local label is out of scope in its own block, so nested joins are
nonrecursive by construction.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Acyclic

open LetCase.LocallyNameless

variable {τ : Type u} [TypeFormers τ]

/-- A scoped operand with exact typing and no named free variables. -/
abbrev Operand (Φ : Type v) [HasTy Φ τ] {n : Nat} (β : BoundCtx τ n) (A : τ) :=
  (t : LetCase.LocallyNameless.Tm Empty Φ n) × Derivation Φ (.nil : Ctx Empty τ) β t A

/-- A structured λSSA region with a single external exit of type `A`. -/
inductive Code (Φ : Type v) [HasTy Φ τ] : {n : Nat} → BoundCtx τ n → τ → Type (max u v)
  | br {n : Nat} {β : BoundCtx τ n} {A : τ} : Operand Φ β A → Code Φ β A
  | let₁ {n : Nat} {β : BoundCtx τ n} {A B : τ} :
      Operand Φ β A → Code Φ (β.snoc A) B → Code Φ β B
  | let₂ {n : Nat} {β : BoundCtx τ n} {A B C : τ} :
      Operand Φ β (product A B) → Code Φ ((β.snoc A).snoc B) C → Code Φ β C
  | case {n : Nat} {β : BoundCtx τ n} {A B C : τ} :
      Operand Φ β (coprod A B) → Code Φ (β.snoc A) C → Code Φ (β.snoc B) C → Code Φ β C
  | join {n : Nat} {β : BoundCtx τ n} {A B : τ} :
      Code Φ β A → Code Φ (β.snoc A) B → Code Φ β B

variable {Φ : Type v} [HasTy Φ τ]

namespace Code

/-- Read the structured code in the existing λSSA syntax. The join block
can only transfer out of the enclosing CFG (its exit index is shifted by one). -/
def toSSA : {n : Nat} → {β : BoundCtx τ n} → {A : τ} → Code Φ β A → Nat → Region Φ
  | _, _, _, .br a, exit => .br exit (Morphism.CaseSSA.erase a.1)
  | _, _, _, .let₁ a body, exit => .let₁ (Morphism.CaseSSA.erase a.1) (body.toSSA exit)
  | _, _, _, .let₂ a body, exit => .let₂ (Morphism.CaseSSA.erase a.1) (body.toSSA exit)
  | _, _, _, .case e left right, exit =>
      .case (Morphism.CaseSSA.erase e.1) (left.toSSA exit) (right.toSSA exit)
  | _, _, _, .join entry block, exit =>
      .cfg (entry.toSSA 0) 1 (fun _ => block.toSSA (exit + 1))

/-- Eliminate each local label using one LetCase binder. Its argument runs
once before the continuation, which sees the incoming payload at index zero. -/
def toLetCase : {n : Nat} → {β : BoundCtx τ n} → {A : τ} → Code Φ β A → Operand Φ β A
  | _, _, _, .br a => a
  | _, _, _, .let₁ a body =>
      let b := body.toLetCase
      ⟨.let₁ a.1 b.1, .let₁ a.2 b.2⟩
  | _, _, _, .let₂ a body =>
      let b := body.toLetCase
      ⟨.let₂ a.1 b.1, .let₂ a.2 b.2⟩
  | _, _, _, .case e left right =>
      let l := left.toLetCase
      let r := right.toLetCase
      ⟨.case e.1 l.1 r.1, .case e.2 l.2 r.2⟩
  | _, _, _, .join entry block =>
      let a := entry.toLetCase
      let b := block.toLetCase
      ⟨.let₁ a.1 b.1, .let₁ a.2 b.2⟩

/-- Reify LetCase in structured SSA. The outer binding and control constructs
become region constructors, and the remaining expressions become operands. -/
def ofLetCase : {n : Nat} → {β : BoundCtx τ n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} → {A : τ} →
    Derivation Φ (.nil : Ctx Empty τ) β t A → Code Φ β A
  | _, _, _, _, .let₁ a b => .join (ofLetCase a) (ofLetCase b)
  | _, _, _, _, .let₂ a b => .let₂ ⟨_, a⟩ (ofLetCase b)
  | _, _, _, _, .case e l r => .case ⟨_, e⟩ (ofLetCase l) (ofLetCase r)
  | _, _, _, _, .fv (x := x) _ => nomatch x
  | _, _, _, _, .bv => .br ⟨_, .bv⟩
  | _, _, _, _, .op a => .br ⟨_, .op a⟩
  | _, _, _, _, .unit => .br ⟨_, .unit⟩
  | _, _, _, _, .pair a b => .br ⟨_, .pair a b⟩
  | _, _, _, _, .inl a => .br ⟨_, .inl a⟩
  | _, _, _, _, .inr a => .br ⟨_, .inr a⟩
  | _, _, _, _, .abort a => .br ⟨_, .abort a⟩

end Code
end Silmaril.Isotope.LambdaSSA.Acyclic
