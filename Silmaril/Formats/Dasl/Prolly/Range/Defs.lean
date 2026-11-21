module

public import Silmaril.Formats.Dasl.Prolly.Scan.Defs
public import Silmaril.Semantics.Prolly.Routing.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly.Range

open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block Node)

variable {Name Key Payload : Type} [LinearOrder Key]

def includes (lower upper key : Key) : Bool := decide (lower ≤ key ∧ key < upper)

def mapSlice (lower upper : Key) (map : OrderedMap Key Payload) : OrderedMap Key Payload :=
  ⟨map.entries.filter fun entry => includes lower upper entry.1, map.ordered.sublist List.filter_sublist⟩

structure Result (Key Payload : Type) where
  entries : List (Key × Payload)
  visits : Nat
  deriving DecidableEq

/-- Selected block occurrences in the reference tree, not distinct addresses,
byte traffic or comparison cost. Only maxima below `lower` are pruned. -/
def selectedVisits (lower : Key) : (level : Nat) → Node Key Payload level → Nat
  | 0, _ => 1
  | level + 1, children => 1 + (children.map fun child =>
      if lower ≤ child.1 then selectedVisits lower level child.2 else 0).sum

/-- Scan `[lower, upper)` in ascending order. Do not fetch a child whose
maximum is strictly below `lower`. Trustworthy pruning requires a reference
with truthful separators. A selected child fault aborts the whole answer. -/
def scan (read : Name → Except (Fault Name) (Block Name Key Payload)) (width : Nat) (lower upper : Key) :
    (fuel : Nat) → Option Nat → Name → Except (Fault Name) (Result Key Payload)
  | 0, _, name => .error (.fuel name)
  | fuel + 1, expected, name => do
    match ← read name with
    | .leaf entries =>
      if (expected = none ∨ expected = some 0) ∧ entries.length ≤ width ∧
          entries.Pairwise (fun left right => left.1 < right.1) then
        .ok ⟨entries.filter fun entry => includes lower upper entry.1, 1⟩
      else .error (.invalidNode name)
    | .branch level children =>
      if (expected = none ∨ expected = some level) ∧ 0 < level ∧ 0 < children.length ∧ children.length ≤ width ∧
          children.Pairwise (fun left right => left.1 < right.1) then do
        let groups ← children.mapM fun child =>
          if lower ≤ child.1 then scan read width lower upper fuel (some (level - 1)) child.2 else .ok ⟨[], 0⟩
        .ok ⟨groups.flatMap Result.entries, 1 + (groups.map Result.visits).sum⟩
      else .error (.invalidNode name)

end Silmaril.Formats.Dasl.Prolly.Range
