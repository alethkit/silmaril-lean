module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Growth

inductive Width where
  | one | two
  deriving DecidableEq, Repr

/-- The entry count at which the next miss requests a grow. -/
def Width.limit : Width → Nat
  | .one => 8
  | .two => 13

def Width.home (width : Width) (hash : UInt32) : UInt32 :=
  match width with
  | .one => 0
  | .two => hash &&& 1

/-- The linked insertion order determines all occupied slots when keys
are never deleted. The bound stops before the second grow. -/
structure Table where
  width : Width
  entries : List Row
  bounded : entries.length ≤ width.limit

def Table.empty : Table := ⟨.one, [], by decide⟩

def Table.keys (table : Table) : List Value :=
  table.entries.map Row.key

/-- Rank references by insertion order within the selected home chain. -/
def homeRows (width : Width) (entries : List Row) (hash : UInt32) : List (Row × Nat) :=
  entries.zipIdx.filter fun item => width.home item.1.hash == width.home hash

def Table.homeEntries (table : Table) (hash : UInt32) : List (Row × Nat) :=
  homeRows table.width table.entries hash

/-- An overflow block starts in slot zero. Later entries use its highest
free slot. Its occupied order differs from the primary block. -/
def overflowOrder {α : Type} : List α → List α
  | [] => []
  | first :: later => first :: later.reverse

def slotOrder {α : Type} (entries : List α) : List α :=
  (entries.take 8).reverse ++ overflowOrder (entries.drop 8)

def primarySlots {α : Type} (entries : List α) : List (Option α) :=
  let primary := entries.take 8
  List.replicate (8 - primary.length) none ++ primary.reverse.map some

def overflowSlots {α : Type} : List α → List (Option α)
  | [] => []
  | first :: later => some first :: (List.replicate (7 - later.length) none ++ later.reverse.map some)

def physicalChain {α : Type} (entries : List α) : List (Option α) :=
  primarySlots entries ++ overflowSlots (entries.drop 8)

def Table.slots (table : Table) (hash : UInt32) : List (Option (Row × Nat)) :=
  physicalChain (table.homeEntries hash)

def orderedCandidates (width : Width) (entries : List Row) (hash : UInt32) : List (Row × Nat) :=
  (slotOrder (homeRows width entries hash)).filter fun item => item.1.hash == hash

def Table.candidates (table : Table) (hash : UInt32) : List (Row × Nat) :=
  orderedCandidates table.width table.entries hash

/-- The placement produced by rehashing the original insertion order at the
wider mask. The stored rows already contain their normalized hash words. -/
def Table.grow (table : Table) (one : table.width = .one) : Table :=
  ⟨.two, table.entries, by have h := table.bounded; rw [one] at h; exact Nat.le_trans h (by decide)⟩

def Table.insert (table : Table) (row : Row) (room : table.entries.length < table.width.limit) : Table :=
  ⟨table.width, table.entries ++ [row], by simpa using Nat.succ_le_of_lt room⟩

def Table.replace (table : Table) (hit : Row × Nat) (value : Value) : Table :=
  ⟨table.width, table.entries.set hit.2 { hit.1 with value }, by simpa using table.bounded⟩

def probeRows (heap : Heap) (width : Width) (entries : List Row) (key : Value) (hash : UInt32) :
    Except Error (Option (Row × Nat)) :=
  (Comparison.probe
    (fun candidate => Comparison.equalAt heap Comparison.defaultDepth key candidate.1.key)
    (orderedCandidates width entries hash)).mapError .runtime

def probeTable (heap : Heap) (table : Table) (key : Value) (hash : UInt32) :
    Except Error (Option (Row × Nat)) :=
  probeRows heap table.width table.entries key hash

def lookupWithHash (heap : Heap) (table : Table) (key : Value) :
    Except Error (UInt32 × Option (Row × Nat)) := do
  let word ← hashKey heap key
  let hash := storedHash word
  let hit ← probeTable heap table key hash
  pure (hash, hit)

/-- Each replay step recomputes its stored hash and probes the already
reinserted prefix before appending to the insertion list. -/
inductive Reinserts (heap : Heap) (width : Width) : List Row → List Row → Prop where
  | done (prefixRows : List Row) : Reinserts heap width prefixRows []
  | next {prefixRows : List Row} {row : Row} {remaining : List Row} {word : UInt32} :
      hashKey heap row.key = .ok word →
      storedHash word = row.hash →
      probeRows heap width prefixRows row.key row.hash = .ok none →
      prefixRows.length < width.limit →
      Reinserts heap width (prefixRows ++ [row]) remaining →
      Reinserts heap width prefixRows (row :: remaining)

def get (heap : Heap) (table : Table) (key : Value) : Except Error (Option Value) :=
  (lookupWithHash heap table key).map fun (_, hit) => hit.map fun item => item.1.value

def commit (table : Table) (row : Row) (hit : Option (Row × Nat)) : Except Error Table :=
  match hit with
  | some item => .ok (table.replace item row.value)
  | none =>
    if room : table.entries.length < table.width.limit then .ok (table.insert row room)
    else .error .capacity

/-- Probe before checking overload. A first grow retries the same hash in
the wider table. A miss at the second threshold is a profile rejection. -/
def set (heap : Heap) (table : Table) (key value : Value) : Except Error Table := do
  let (hash, hit) ← lookupWithHash heap table key
  let row : Row := ⟨hash, key, value⟩
  match hit with
  | some item => pure (table.replace item value)
  | none =>
    if grow : table.width = .one ∧ table.entries.length = 8 then
      let expanded := table.grow grow.1
      commit expanded row (← probeTable heap expanded key hash)
    else commit table row none

def contains (heap : Heap) (table : Table) (key : Value) : Except Error Bool :=
  Option.isSome <$> observeLookup (get heap table key)

def equalWith (heap : Heap) (compare : Nat → Value → Value → Except Error Bool) :
    Nat → Table → Table → Except Error Bool
  | 0, _, _ => .error (.runtime .comparisonDepth)
  | depth + 1, left, right =>
    if left.entries.length = right.entries.length then compareRows (get heap right) (compare depth) left.entries
    else .ok false

end Silmaril.Languages.Starlark.Lists.GoDictionary.Growth
