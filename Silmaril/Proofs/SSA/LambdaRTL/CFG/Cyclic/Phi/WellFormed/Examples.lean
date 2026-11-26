module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.WellFormed.Thms

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA.Examples

/-- Register 1 is defined by the header's φ. Register 2 is defined in the
latch and can be read on the backedge, after that definition. -/
private def loop : Graph Nat Nat Unit :=
  ⟨.term (br 10),
    [(10, ⟨[⟨1, [(none, .var 0), (some 20, .var 2)]⟩],
      .term (.case (.app () (.var 1)) 3 (ret (.var 1)) 4 (br 20))⟩),
     (20, ⟨[], .let1 2 (.app () (.var 1)) (.term (br 10))⟩)]⟩

private def loopCertificate : Certificate Nat Nat := [(10, []), (20, [1])]

example : WellFormed loop [0] := check_sound (cert := loopCertificate) (by decide)
example : (GlobalSSA.compile loop [0] loopCertificate).isSome := by decide

-- A claim at the header must hold on its entry edge as well as its backedge.
example : check loop [0] [(10, [2]), (20, [1])] = false := by decide
example : check loop [0] [(10, [])] = false := by decide

-- Each entry arm defines its own payload. That payload is available on the
-- matching φ edge. The right arm cannot use the left arm's definition.
private def branches (rightOperand : Nat) : Graph Nat Nat Unit :=
  ⟨.term (.case (.val (.var 0)) 1 (br 10) 2 (br 20)),
    [(10, ⟨[⟨3, [(none, .var 1)]⟩], .term (ret (.var 3))⟩),
     (20, ⟨[⟨4, [(none, .var rightOperand)]⟩], .term (ret (.var 4))⟩)]⟩

private def branchCertificate : Certificate Nat Nat := [(10, []), (20, [])]

example : check (branches 2) [0] branchCertificate = true := by decide
example : (Phi.compile (branches 1)).isSome := by decide
example : check (branches 1) [0] branchCertificate = false := by decide
example : (GlobalSSA.compile (branches 1) [0] branchCertificate).isNone := by decide

-- The invalid right edge cannot be justified by a different certificate.
example (certificate : Certificate Nat Nat) : check (branches 1) [0] certificate = false := by
  cases accepted : check (branches 1) [0] certificate with
  | false => rfl
  | true =>
      let right : Route Nat Nat := ⟨some 20, [.read [0], .define [2], .read [1]]⟩
      have chosen : right ∈ routes (branches 1) none :=
        List.mem_cons_of_mem _ List.mem_cons_self
      have available : [1] ⊆ ([0] ++ Access.definitions [.read [0], .define [2]]) :=
        (check_sound accepted).available EntryPath.entry chosen rfl
      exact False.elim ((by decide : 1 ∉ ([0] ++ Access.definitions [.read [0], .define [2]]))
        (available List.mem_cons_self))

-- Reachability concerns uses. Unreachable names still participate in static uniqueness.
private def deadUse : Graph Nat Nat Unit :=
  { loop with blocks := loop.blocks ++ [(30, ⟨[], .term (ret (.var 99))⟩)] }

private def duplicateDefinition : Graph Nat Nat Unit :=
  { loop with blocks := loop.blocks ++ [(30, ⟨[], .let1 2 (.val .unit) (.term (ret .unit))⟩)] }

example : check deadUse [0] loopCertificate = true := by decide
example : duplicateDefinition.check = true := by decide
example : check duplicateDefinition [0] loopCertificate = false := by decide

private def forwardUse : Graph Nat Nat Unit :=
  ⟨.let1 1 (.val (.var 2)) (.let1 2 (.val .unit) (.term (ret (.var 1)))), []⟩

example : forwardUse.check = true := by decide
example : check forwardUse [] [] = false := by decide

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA.Examples
