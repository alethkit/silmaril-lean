module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Defs

/-! # Discover a Store for cross-activation forwarding -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search

open RVSDG (Port Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}

/-- The memory version and original address argument of a Store. An address
from a local producer has no argument port to put in a certificate. -/
abbrev StoreSite (args : List ValueSort) := Nat × Option (Port args .address)

/-- Enumerate Store occurrences in the original table order. -/
def stores : {past : List (List ValueSort)} → {version : Nat} →
    Memory.Body args past version → List (StoreSite args)
  | _, _, .ret _ _ => []
  | _, _, .load _ _ rest => stores rest
  | _, version, .store _ (.arg writer) _ rest => (version + 1, some writer) :: stores rest
  | _, version, .store _ (.output _ _) _ rest => (version + 1, none) :: stores rest

/-- Search newest first. The first matching Store is selected, and each
more recent Store contributes its exact original writer port. -/
def select (observed : Port args .address) :
    List (StoreSite args) → Option (Nat × List (Port args .address))
  | [] => none
  | (_, none) :: _ => none
  | (version, some writer) :: rest =>
    if writer.index = observed.index then some (version, [])
    else (select observed rest).map (fun (found, writers) => (found, writer :: writers))

def capturedAddress (source : Loop.Graph args) : Option (Port args .address) :=
  match source.body with
  | .load _ (.arg address) _ => some address
  | _ => none

structure Result (args : List ValueSort) where
  graph : Graph args
  facts : Certificate args

/-- Discover a candidate and run the existing native rewrite checker.
The returned certificate is an obligation on each invocation. -/
def discover (source : Loop.Graph args) : Option (Result args) := do
  let observed ← capturedAddress source
  let (version, writers) ← select observed (stores source.body).reverse
  let facts : Certificate args := ⟨observed, writers⟩
  let target ← Carried.rewriteWith source version facts
  some ⟨target, facts⟩

/-- Admit the discovered graph when the concrete cells satisfy its facts. -/
def discoverChecked (source : Loop.Graph args) (input : Tuple (Val cells) args) :
    Option (Result args) := do
  let result ← discover source
  if result.facts.check input then some result else none

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search
