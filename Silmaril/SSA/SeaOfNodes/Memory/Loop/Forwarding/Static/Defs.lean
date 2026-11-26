module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Defs

/-! # Static load forwarding with reported address assumptions -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static

open RVSDG (Origin)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {past : List (List ValueSort)}

/-- Read the selected Load's address and collect Store arguments strictly
after the nominated Store and before that Load. A Store at input version
`version` publishes version `version + 1`. A Store to the observed port
would require that cell to differ from itself. -/
def requiredFactsAt (storeVersion : Nat) :
    {past : List (List ValueSort)} → {version : Nat} →
    Memory.Body args past version → Nat → Option (Certificate args)
  | _, _, .ret _ _, _ => none
  | _, _, .load _ (.arg port) _, 0 => some ⟨port, []⟩
  | _, _, .load _ (.output _ _) _, 0 => none
  | _, _, .load _ _ rest, index + 1 => requiredFactsAt storeVersion rest index
  | _, _, .store _ _ _ _, 0 => none
  | _, version, .store _ address _ rest, index + 1 =>
    let facts := requiredFactsAt storeVersion rest index
    if storeVersion ≤ version then
      match address with
      | .arg writer => do
        let found ← facts
        if found.matches address then none
        else some { found with writers := writer :: found.writers }
      | .output _ _ => none
    else facts

structure Result (args : List ValueSort) where
  graph : Graph args
  facts : Certificate args

/-- Compute one native loop rewrite from the original wires. The existing
structural checker verifies the nominated Store, all covered writers, and
the resulting loop's admission. `facts.Valid` is the input contract. -/
def rewrite (graph : Graph args) (candidate : Memory.Forwarding.Candidate) : Option (Result args) := do
  let facts ← requiredFactsAt candidate.storeVersion graph.body candidate.loadIndex
  let rewritten ← Memory.Loop.Forwarding.rewriteWith graph candidate facts
  some ⟨rewritten, facts⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static
