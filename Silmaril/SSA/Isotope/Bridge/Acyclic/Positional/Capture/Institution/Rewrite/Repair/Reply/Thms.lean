module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Normalize

/-! # Replaying the effectful reply-tree normal form -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

open Isotope.LetCase.LocallyNameless (AbortEquiv)

/-- Replay native `bindCase` at an effectful discriminator, then normalize
each selected continuation under its payload binder. -/
theorem Tree.normalize_operand (p : Tree) {n : Nat} (β : BoundCtx Sorts n) :
    AbortEquiv false (Ctx.nil : Ctx Empty Sorts) β
      (p.operand β).1 (p.normal.render.operand β).1 Ty.unit :=
  normalize_operand_proof p β

theorem repaired_of_normal (tail : List Sorts) (p q : Tree) (h : p.normal = q.normal) :
    Repaired false (equation tail p q) :=
  repaired_of_normal_proof tail p q h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
