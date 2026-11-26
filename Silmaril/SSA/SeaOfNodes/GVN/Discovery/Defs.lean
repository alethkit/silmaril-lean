module

public import Silmaril.SSA.SeaOfNodes.GVN.Defs

/-! Exhaustive representative discovery for one candidate in a pure table. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Discovery

open Diamond (Dataflow Signature Ty ValueSort)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {out : ValueSort Data} {flow : Dataflow Op args past sigs}

/-- Zero-based position in the supplied table, excluding its initial scope. -/
def position :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → Producer flow out → Nat
  | _, _, _, _, .here => 0
  | _, _, _, _, .later ref => (position ref).succ

variable [DecidableEq (ValueSort Data)]

/-- Enumerate the same-sort producers strictly before the candidate in table order. -/
def earlier :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → (candidate : Producer flow out) → List (Producer flow out)
  | _, _, _, _, .here => []
  | scope, _, _, out, .later (out := head) (op := op) (inputs := inputs) (rest := rest) next =>
    let tail := (earlier (past := scope ++ [[.value head]]) next).map
      (Producer.later (op := op) (inputs := inputs))
    if same : head = out then
      (same ▸ Producer.here (op := op) (inputs := inputs) (rest := rest)) :: tail
    else tail

/-- The first accepted earlier producer, with the original typed wire available
through `Producer.origin`. -/
def findRepresentative? [∀ ins out, DecidableEq (Op ins out)]
    (candidate : Producer flow out) : Option (Producer flow out) :=
  (earlier candidate).find? (checkRepresentative candidate)

end Silmaril.SSA.SeaOfNodes.GVN.Discovery
