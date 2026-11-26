module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs

/-! # A typed acyclic fragment for syntactic round trips -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Acyclic

open LetCase.LocallyNameless (Derivation)
open Isotope.Morphism.CaseSSA (erase)
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A returned sum case selects between constructor arms that use only their
bound payload. The whole case has one sum input. -/
def Operand.caseReturn {n : Nat} {β : BoundCtx τ n} {A B D : τ}
    (scrutinee : Operand Φ β (coprod A B))
    (left : Operand Φ (β.snoc A) D) (right : Operand Φ (β.snoc B) D) : Prop :=
  β.toList = [coprod A B] ∧ erase scrutinee.1 = .var 0 ∧
    ∃ l r : Tm Φ, Tm.BranchValue [A] l D ∧ Tm.BranchValue [B] r D ∧
      erase left.1 = l.rename (lift Nat.succ) ∧ erase right.1 = r.rename (lift Nat.succ)

/-- Admitted returned operands have a branch head, recursively admitted unary
lets, or a detached constructor case at the single sum input. -/
def Operand.admittedDerivation : {n : Nat} → {β : BoundCtx τ n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → {A : τ} →
    Derivation Φ (.nil : Ctx Empty τ) β t A → Prop
  | _, _, _, _, .let₁ a b => admittedDerivation a ∧ admittedDerivation b
  | _, _, _, _, .let₂ _ _ => False
  | _, _, _, _, .case e l r => caseReturn ⟨_, e⟩ ⟨_, l⟩ ⟨_, r⟩
  | _, _, _, _, _ => True

abbrev Operand.Admitted {n : Nat} {β : BoundCtx τ n} {A : τ} (a : Operand Φ β A) : Prop :=
  admittedDerivation a.2

/-- All structured code constructors are admitted. Reification treats branch
operands and unary-let scrutinees as code, so these operands must be admitted.
Region case and binary-let scrutinees are reused directly. -/
def Code.Admitted : {n : Nat} → {β : BoundCtx τ n} → {A : τ} → Code Φ β A → Prop
  | _, _, _, .br a => a.Admitted
  | _, _, _, .let₁ a b => a.Admitted ∧ b.Admitted
  | _, _, _, .let₂ _ b => b.Admitted
  | _, _, _, .case _ l r => l.Admitted ∧ r.Admitted
  | _, _, _, .join e b => e.Admitted ∧ b.Admitted

/-- The literal output of the existing SSA embedding, with every outgoing
argument evaluated once and bound before its branch. -/
def Code.guardedSSA {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code Φ β A) (exit : Nat) : Region Φ :=
  (c.toSSA exit).bindBranchArguments

/-- Use the existing unary return fusion and the pure case-return rule. -/
abbrev RoundTripSeed {ε : Type w} [HasEff Φ ε] (pe : ε)
    (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  Region.Paper.WithCaseAndUnaryReturns.Step pe Γ r s L

end Silmaril.Isotope.LambdaSSA.Acyclic
