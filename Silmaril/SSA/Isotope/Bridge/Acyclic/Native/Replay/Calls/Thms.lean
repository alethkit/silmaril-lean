module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls

/-! # Exact reifier replay for ordered primitive calls -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region (ValueBranches)
open Region.Paper.WithComputedCallReturns
open Morphism.CaseSSA (erase)
open LetCase.Structural.Finite (Context Types)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

section Schedule

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B : τ} {r s : Region Φ} {fs gs : List Φ}

/-- The scheduled region types at the original singleton exit. -/
theorem CallSchedule.valueBranches (p : CallSchedule Γ r A fs) : ValueBranches Γ r [A] :=
  p.valueBranches_proof

/-- Continuation composition preserves captures and concatenates call order. -/
theorem CallSchedule.splice (p : CallSchedule Γ r A fs) (q : CallSchedule (A :: Γ) s B gs) :
    CallSchedule Γ (r.lsubst (fun _ => s)) B (fs ++ gs) :=
  p.splice_proof q

/-- The literal guarded return and the actual reification of an admitted
exact operand replay to the same typed region in source call order. -/
theorem operand_schedule {ε : Type w} [HasEff Φ ε] (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {D : τ} (a : Operand Φ β D)
    (shape : CallOperand (erase a.1)) :
    ∃ r, CallSchedule β.toList r D (operandCalls (erase a.1)) ∧
      ConstructorJoin.Eqv pe β.toList ((Code.br a).guardedSSA 0) r [D] ∧
      ConstructorJoin.Eqv pe β.toList ((Code.ofLetCase a.2).guardedSSA 0) r [D] :=
  operand_schedule_proof pe a shape

end Schedule

/-- At a written guarded outward endpoint, an admitted compilation suffices
to replay ordered calls back to the original region. -/
theorem Endpoint.call_schedule {Φ : Type} [LetCase.Structural.Finite.Signature Φ]
    {n : Nat} {β : Context n} {A : Types} (p : Endpoint Φ β A)
    (guarded : ValueBranches β.toList p.region [A]) (shape : CallOperand (erase p.compile.1)) :
    ∃ r, CallSchedule β.toList r A (operandCalls (erase p.compile.1)) ∧
      ConstructorJoin.Eqv false β.toList p.region r [A] :=
  call_schedule_proof p guarded shape

/-- The extra computed-call step is sound at the original typed outward
arrows under the same #4334 model assumptions. -/
theorem Endpoint.call_sound {Φ : Type} [LetCase.Structural.Finite.Signature Φ]
    {n : Nat} {β : Context n} {A : Types} {p q : Endpoint Φ β A}
    (h : p.CallEqv q) : p.Valid q :=
  call_sound_proof h

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
