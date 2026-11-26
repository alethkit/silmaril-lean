module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Defs

/-! # Discover one same-activation Load forwarding rewrite -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Search

open Memory.Forwarding (Candidate)

variable {args : List ValueSort}

/-- Visit Loads in original table order. At each Load, visit the preceding
Stores from newest to oldest. The body's version index counts preceding
Stores, and version zero denotes the incoming heap. -/
def candidates (graph : Graph args) : List Candidate :=
  fromBody graph.body 0
where
  fromBody : {past : List (List ValueSort)} → {version : Nat} →
      Memory.Body args past version → Nat → List Candidate
    | _, _, .ret _ _, _ => []
    | _, version, .load _ _ rest, index =>
      ((List.range' 1 version).reverse.map fun storeVersion => ⟨storeVersion, index⟩) ++
        fromBody rest (index + 1)
    | _, _, .store _ _ _ rest, index => fromBody rest (index + 1)

/-- Apply the static checker to the first pair it accepts. The result's
`facts.Valid` remains an obligation on each invocation. -/
def rewrite (graph : Graph args) : Option (Static.Result args) :=
  (candidates graph).findSome? (Static.rewrite graph)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Static.Search
