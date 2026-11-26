module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.ConstructorJoin.Defs

/-! # A typed call schedule for native operand replay -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open LetCase.Structural.Finite (Context Types)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-- Allow arbitrary unary sequencing and recursively computed primitive
arguments. Assembly can use bound replies and pure constructor expressions. -/
def CallOperand {Φ : Type*} (t : Tm Φ) : Prop :=
  match t with
  | .op _ a => CallOperand a
  | .let₁ a b => CallOperand a ∧ CallOperand b
  | _ => ConstructorOnly t

/-- Source order for the admitted operand grammar. -/
def operandCalls {Φ : Type*} : Tm Φ → List Φ
  | .op f a => operandCalls a ++ [f]
  | .let₁ a b => operandCalls a ++ operandCalls b
  | _ => []

/-- A literal region whose primitive arguments are constructor values.
The type and order of the calls are part of the judgment. -/
inductive CallSchedule {τ : Type*} [TypeFormers τ] {Φ : Type*} [HasTy Φ τ] :
    VCtx τ → Region Φ → τ → List Φ → Prop where
  | ret {Γ : VCtx τ} {a : Tm Φ} {A : τ} (value : Tm.BranchValue Γ a A) :
      CallSchedule Γ (.br 0 a) A []
  | call {Γ : VCtx τ} {f : Φ} {a : Tm Φ} {r : Region Φ} {A : τ} {fs : List Φ}
      (value : Tm.BranchValue Γ a (instrSrc f))
      (cont : CallSchedule (instrTrg f :: Γ) r A fs) :
      CallSchedule Γ (.let₁ (.op f a) r) A (f :: fs)

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

abbrev Endpoint.CallEqv (p q : Endpoint Φ β A) : Prop :=
  Region.Paper.WithComputedCallReturns.ConstructorJoin.Eqv false β.toList p.region q.region [A]

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
