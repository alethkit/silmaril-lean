module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

open Isotope.LetCase.LocallyNameless (AbortEquiv Equiv HasType Refinement)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)

theorem normalize_operand_proof (p : Tree) {n : Nat} (β : BoundCtx Sorts n) :
    AbortEquiv false Γ₀ β (p.operand β).1 (p.normal.render.operand β).1 U := by
  induction p generalizing n with
  | returnUnit => exact .equiv (.refl .unit)
  | emit bit next ih => exact .let₁ (.equiv (.refl (.op .unit))) (ih (β.snoc U))
  | stop fault sequenced =>
    cases sequenced
    · exact .equiv (.refl (.abort (.op .unit)))
    · let d : HasType signature.Instr Γ₀ β (.op (.stop fault) .unit) Ty.empty := .op .unit
      exact (AbortEquiv.sequence (pe := false) (A := U) d).symm
  | ask req bound l r ihl ihr =>
    let d : HasType signature.Instr Γ₀ β (.op (.ask req) .unit) Answer := .op .unit
    have normalize := Refinement.case (.equiv (.refl d)) (ihl (β.snoc U)) (ihr (β.snoc U))
    cases bound
    · exact normalize
    · have once := Equiv.bindCase (pureEff := false) d
        (l.operand (β.snoc U)).2.toHasType (r.operand (β.snoc U)).2.toHasType
      exact .trans (.equiv once.symm) normalize

theorem repaired_of_normal_proof (tail : List Sorts) (p q : Tree) (h : p.normal = q.normal) :
    Repaired false (equation tail p q) := by
  have left := normalize_operand_proof p .nil
  rw [h] at left
  exact .let₁ (left.trans (normalize_operand_proof q .nil).symm)
    (.equiv (.refl (.let₁ .bv (.inl .bv))))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
