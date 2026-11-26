module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

open Isotope.LetCase.LocallyNameless (AbortCongr Derivation)

set_option backward.isDefEq.respectTransparency false

private theorem normalize_operand (p : Body) {n : Nat} (β : BoundCtx Sorts n) :
    AbortCongr (Ctx.nil : Ctx Empty Sorts) (p.operand β).2 (p.canonical.operand β).2 := by
  induction p generalizing n with
  | returnUnit => exact .refl _
  | emit bit next ih => exact .let₁ (.refl _) (ih (β.snoc Ty.unit))
  | stop bit seq =>
    cases seq
    · exact .refl _
    · let d : Derivation signature.Instr (Ctx.nil : Ctx Empty Sorts) β (.op (.stop bit) .unit) Ty.empty :=
        .op .unit
      exact (AbortCongr.sequence (A := Ty.unit) d).symm

private theorem normalize_packed (tail : List Sorts) (p : Body) :
    AbortCongr (Ctx.nil : Ctx Empty Sorts) (Rewrite.returnUnit tail (p.operand .nil)).toLetCase.2
      (Rewrite.returnUnit tail (p.canonical.operand .nil)).toLetCase.2 :=
  .let₁ (normalize_operand p .nil) (.refl _)

theorem sequencesEmpty_normal_proof (tail : List Sorts) (p q : Body) (h : p.normal = q.normal) :
    SequencesEmpty (equation tail p q) := by
  have canonical : p.canonical = q.canonical :=
    congrArg (fun nf : Normal => Normal.body nf.1 nf.2) h
  have left := normalize_packed tail p
  rw [canonical] at left
  exact left.trans (normalize_packed tail q).symm

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
