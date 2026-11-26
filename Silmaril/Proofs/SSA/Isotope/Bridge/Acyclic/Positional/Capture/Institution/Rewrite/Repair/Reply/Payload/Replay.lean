module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

open Isotope.LetCase.LocallyNameless (Equiv HasType Tm)
open LambdaSSA (At)
open LambdaSSA.Acyclic (Operand FiniteExit)
open LambdaSSA.Region (packedExitType)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)

private theorem unit_slot {n : Nat} (β : BoundCtx Sorts n) :
    Equiv false Γ₀ (β.snoc U) (.bv 0 : Tm Empty signature.Instr (n + 1)) .unit U := by
  let d : HasType signature.Instr Γ₀ (β.snoc U) (.bv 0) U := .bv
  exact (Equiv.unitEta d).symm.trans (Equiv.letBeta .bv d .unit)

theorem expr_replay_proof (e : Expr) {n : Nat} (β : BoundCtx Sorts n) (i : Fin n)
    (h : β.get i = Bit) :
    Equiv false Γ₀ β (e.operand β i h).1
      ((Expr.table (e.evaluate false) (e.evaluate true)).operand β i h).1 Bit := by
  cases e with
  | table l r => exact .refl ((Expr.table l r).operand β i h).2.toHasType
  | payload =>
    let d := (readPayload β i h).2.toHasType
    exact (Equiv.caseEta (pureEff := false) d).symm.trans
      (.case (.refl d) (.inl (unit_slot β)) (.inr (unit_slot β)))

private theorem tag_congr {n : Nat} {β : BoundCtx Sorts n} (L : List Sorts) (i : Nat)
    {A : Sorts} (h : At L i A) (a b : Operand signature.Instr β A)
    (eq : Equiv false Γ₀ β a.1 b.1 A) :
    Equiv false Γ₀ β (FiniteExit.tag L i h a).1 (FiniteExit.tag L i h b).1 (packedExitType L) := by
  induction L generalizing i with
  | nil => cases i <;> contradiction
  | cons B L ih =>
    cases i with
    | zero =>
      have e : B = A := Option.some.inj h
      cases e
      exact .inl eq
    | succ i => exact .inr (ih i h)

private theorem arm_replay {L : List Sorts} (a : Arm L) (effects : List Bool)
    {n : Nat} (β : BoundCtx Sorts n) (i : Fin n) (h : β.get i = Bit) :
    Equiv false Γ₀ β (a.renderPrefix effects β i h).1
      (a.normal.render.renderPrefix effects β i h).1 (packedExitType L) := by
  induction effects generalizing n with
  | nil => exact tag_congr L _ _ _ _ (expr_replay_proof a.result β i h)
  | cons b effects ih => exact .let₁ (.refl (.op .unit)) (ih (β.snoc U) i.succ h)

theorem entry_replay_proof {L : List Sorts} (p : ProgramBody L) :
    Equiv false Γ₀ .nil p.entry.1 p.normal.render.entry.1 (packedExitType L) := by
  obtain ⟨req, bound, l, r⟩ := p
  let d : HasType signature.Instr Γ₀ .nil (.op (.ask req) .unit) Answer := .op .unit
  have normal := Equiv.case (.refl d)
    (arm_replay l l.emits (.snoc .nil Bit) 0 rfl)
    (arm_replay r r.emits (.snoc .nil Bit) 0 rfl)
  cases bound
  · exact normal
  · have once := Equiv.bindCase (pureEff := false) d
      (l.operand .nil).2.toHasType (r.operand .nil).2.toHasType
    exact once.symm.trans normal

theorem derive_normal_proof (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L))
    (h : p.normal = q.normal) : Derivable false (equation H L p q) := by
  have replay := entry_replay_proof p
  rw [h] at replay
  exact .let₁ (replay.trans (entry_replay_proof q).symm)
    (.refl ((program H L p).body.render .base).encode.toLetCase.2.toHasType)

theorem derive_render_proof (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    Derivable false (equation H L p p.normal.render) :=
  .let₁ (entry_replay_proof p) (.refl ((program H L p).body.render .base).encode.toLetCase.2.toHasType)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
