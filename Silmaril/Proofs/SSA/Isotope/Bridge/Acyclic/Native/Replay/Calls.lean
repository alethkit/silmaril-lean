module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.ConstructorJoin.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region (ValueBranches HasType)
open Region.Paper
open Region.CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Region.Paper.RetainedLet (returnOnce)
open Region.Paper.WithComputedCallReturns
open Morphism.CaseSSA (erase erase_hasType)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Finite (Context Types)
open Silmaril.DeBruijn (lift)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

universe u v w

section Schedule

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A : τ} {r : Region Φ} {fs : List Φ}

theorem CallSchedule.valueBranches_proof (p : CallSchedule Γ r A fs) : ValueBranches Γ r [A] := by
  induction p with
  | ret value => exact .br (ℓ := 0) rfl value
  | call value _ ih => exact .let₁ (.op value.hasType) ih

omit [HasTy Φ τ] in
private theorem underValueBinder {Γ Δ : VCtx τ} {θ : Nat → Tm Φ}
    (values : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) (B : τ) :
    ∀ ⦃i T⦄, At (B :: Γ) i T → Tm.BranchValue (B :: Δ) (Tm.liftSubst θ i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact .var rfl
  | succ i =>
    change Tm.BranchValue (B :: Δ) ((θ i).rename Nat.succ) T
    rw [Tm.rename_eq_subst]
    exact (values hi).subst (fun _ _ atSlot => .var (Ren.wk Δ B atSlot))

private theorem CallSchedule.subst {Δ : VCtx τ} {θ : Nat → Tm Φ} (p : CallSchedule Γ r A fs)
    (values : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) :
    CallSchedule Δ (r.substVars θ) A fs := by
  induction p generalizing Δ θ with
  | ret value => exact .ret (value.subst (fun _ _ hi => values hi))
  | call value _ ih =>
    exact .call (value.subst (fun _ _ hi => values hi)) (ih (underValueBinder values _))

private theorem CallSchedule.rename {Δ : VCtx τ} {ρ : Nat → Nat} (p : CallSchedule Γ r A fs)
    (typed : Ren Γ Δ ρ) : CallSchedule Δ (r.renameVars ρ) A fs := by
  rw [Region.renameVars_eq_substVars]
  exact p.subst (fun _ _ hi => .var (typed hi))

/-- Native continuation substitution retains captures below each earlier reply
binder and concatenates exactly the two call lists. -/
theorem CallSchedule.splice_proof {B : τ} {s : Region Φ} {gs : List Φ}
    (p : CallSchedule Γ r A fs) (q : CallSchedule (A :: Γ) s B gs) :
    CallSchedule Γ (r.lsubst (fun _ => s)) B (fs ++ gs) := by
  induction p generalizing s with
  | ret value =>
    apply q.subst
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact value
    | succ i => exact .var hi
  | @call Γ f a r A fs value cont ih =>
    exact .call value (ih (q.rename ((Ren.wk Γ (instrTrg f)).lift A)))

end Schedule

section Replay

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

omit [TypeFormers τ] in
private theorem atSingleton {A T : τ} {i : Nat} (hi : At [A] i T) : i = 0 ∧ T = A := by
  cases i with
  | zero => exact ⟨rfl, (Option.some.inj hi).symm⟩
  | succ i => simp [At] at hi

private theorem spliceEq {Γ : VCtx τ} {A B : τ} {r r' s s' : Region Φ}
    (guarded : ValueBranches Γ r [A]) (guarded' : ValueBranches Γ r' [A])
    (firstEq : ConstructorJoin.Eqv pe Γ r r' [A]) (cont : ConstructorJoin.Eqv pe (A :: Γ) s s' [B]) :
    ConstructorJoin.Eqv pe Γ (r.lsubst (fun _ => s)) (r'.lsubst (fun _ => s')) [B] := by
  have replace : ConstructorJoin.Eqv pe Γ (r.lsubst (fun _ => s)) (r.lsubst (fun _ => s')) [B] :=
    .lsubstCongr guarded (fun _ _ hi => (atSingleton hi).2.symm ▸ cont)
  exact replace.trans (.lsubstPost firstEq guarded guarded'
    (fun _ _ hi => (atSingleton hi).2.symm ▸ cont.typed.2))

private theorem returns_one {Γ : VCtx τ} {A : τ} {t : Tm Φ} (h : Tm.HasType Γ t A) :
    ConstructorJoin.Eqv pe Γ (returnRegion t) (returnOnce t) [A] :=
  UnaryReturn.returnRegion_eq_returnOnce (fun e => .inl (.inl (.inr (.inl e)))) h

private theorem assembly {n : Nat} {β : BoundCtx τ n} {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (.nil : Ctx Empty τ) β t A) (pure : ConstructorOnly (erase t)) :
    ∃ r, CallSchedule β.toList r A [] ∧ ConstructorJoin.Eqv pe β.toList (returnRegion (erase t)) r [A] := by
  obtain ⟨v, normal, _⟩ := constructor_replay pe ⟨t, d⟩ pure
  refine ⟨.br 0 v, .ret normal.typed.2, (returns_one pe (erase_hasType d.toHasType)).trans ?_⟩
  exact ConstructorJoin.ofConstructor
    (WithConstructorSequencing.Joined.ofConstructor (WithConstructorSequencing.returnOnce_eq_branch normal))

private theorem normalize_operand {n : Nat} {β : BoundCtx τ n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (.nil : Ctx Empty τ) β t A) (shape : CallOperand (erase t)) :
    Operand.admittedDerivation d ∧ ∃ r, CallSchedule β.toList r A (operandCalls (erase t)) ∧
      ConstructorJoin.Eqv pe β.toList (returnRegion (erase t)) r [A] := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | bv => exact ⟨trivial, assembly pe .bv shape⟩
  | unit => exact ⟨trivial, assembly pe .unit shape⟩
  | pair a b _ _ => exact ⟨trivial, assembly pe (.pair a b) shape⟩
  | inl a _ => exact ⟨trivial, assembly pe (.inl a) shape⟩
  | inr a _ => exact ⟨trivial, assembly pe (.inr a) shape⟩
  | @let₁ _ β a b A B da db iha ihb =>
    obtain ⟨oka, r, hr, replayA⟩ := iha shape.1
    obtain ⟨okb, s, hs, replayB⟩ := ihb shape.2
    have e := spliceEq pe (returnRegion_typed (erase_hasType da.toHasType))
      hr.valueBranches_proof replayA replayB
    exact ⟨⟨oka, okb⟩, _, hr.splice_proof hs, e⟩
  | @op _ β f a da ih =>
    obtain ⟨_, r, hr, replay⟩ := ih shape
    let next := returnRegion (Tm.op f (.var 0))
    have slot : Tm.BranchValue (instrSrc f :: β.toList) (.var 0 : Tm Φ) (instrSrc f) := .var rfl
    have run : CallSchedule (instrSrc f :: β.toList) next (instrTrg f) [f] :=
      .call slot (.ret (.var (i := 0) rfl))
    have moved := ConstructorJoin.ofCall (pe := pe) (WithComputedCallReturns.Step.seq f (erase_hasType da.toHasType))
    have tail := spliceEq pe (returnRegion_typed (erase_hasType da.toHasType)) hr.valueBranches_proof replay
      (s := next) (.refl run.valueBranches_proof.hasType)
    exact ⟨trivial, _, hr.splice_proof run, moved.trans tail⟩
  | let₂ | case | abort => exact shape.elim

theorem operand_schedule_proof {n : Nat} {β : BoundCtx τ n} {A : τ} (a : Operand Φ β A)
    (shape : CallOperand (erase a.1)) :
    ∃ r, CallSchedule β.toList r A (operandCalls (erase a.1)) ∧
      ConstructorJoin.Eqv pe β.toList ((Code.br a).guardedSSA 0) r [A] ∧
      ConstructorJoin.Eqv pe β.toList ((Code.ofLetCase a.2).guardedSSA 0) r [A] := by
  obtain ⟨admitted, r, scheduled, replay⟩ := normalize_operand pe a.2 shape
  have roundTrip := ConstructorJoin.ofConstructor (operand_roundTrip_constructor pe a admitted)
  have returned := (returns_one pe (erase_hasType a.2.toHasType)).symm.trans replay
  exact ⟨r, scheduled, returned, roundTrip.symm.trans returned⟩

theorem code_admitted_proof (pe : ε) {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code Φ β A)
    (shape : CallOperand (erase c.toLetCase.1)) : c.Admitted := by
  induction c with
  | br a => exact (normalize_operand pe a.2 shape).1
  | let₁ a _ ih => exact ⟨(normalize_operand pe a.2 shape.1).1, ih shape.2⟩
  | join _ _ iha ihb => exact ⟨iha shape.1, ihb shape.2⟩
  | let₂ | case => exact shape.elim

end Replay

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

theorem Endpoint.call_schedule_proof (p : Endpoint Φ β A)
    (guarded : ValueBranches β.toList p.region [A]) (shape : CallOperand (erase p.compile.1)) :
    ∃ r, CallSchedule β.toList r A (operandCalls (erase p.compile.1)) ∧
      ConstructorJoin.Eqv false β.toList p.region r [A] := by
  obtain ⟨r, order, _, replay⟩ := operand_schedule_proof false p.compile shape
  have roundTrip := p.joined_roundTrip (code_admitted_proof false p.code shape) guarded
  exact ⟨r, order, (ConstructorJoin.ofConstructor (WithConstructorSequencing.Joined.ofJoined roundTrip)).trans replay⟩

theorem Endpoint.call_sound_proof {p q : Endpoint Φ β A} (h : p.CallEqv q) : p.Valid q := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central
    M instr regionCoherent _ shared
  exact ConstructorJoin.sound J M shared h p.typed q.typed

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
