module

public import Silmaril.SSA.SeaOfNodes.GVN.Defs

/-! Delete one checked duplicate and route the surviving table and result wires. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Elimination

open Diamond (Dataflow Model Signature Ty Val ValueSort)
open RVSDG (Locals Origin Port Tuple Wires extend)

universe u v w

section Scope

variable {T : Type u} {args : List T} {t : T}
variable {past target : List (List T)}

/-- An output after one binding refers either to the old scope or to a port
of the newly bound tuple. -/
def splitOutput (head : List T) : (scope : List (List T)) →
    (i : Fin (scope ++ [head]).length) → Port (scope ++ [head])[i] t →
    (Σ j : Fin scope.length, Port scope[j] t) ⊕ Port head t
  | [], i => Fin.cases
      (motive := fun j => Port ([] ++ [head])[j] t →
        (Σ k : Fin 0, Port ([] : List (List T))[k] t) ⊕ Port head t)
      Sum.inr (fun j => j.elim0) i
  | first :: tail, i => Fin.cases
      (motive := fun j => Port ((first :: tail) ++ [head])[j] t →
        (Σ k : Fin (first :: tail).length, Port (first :: tail)[k] t) ⊕ Port head t)
      (fun p => .inl ⟨0, p⟩)
      (fun j p => (splitOutput head tail j p).map (fun ⟨k, q⟩ => ⟨k.succ, q⟩) id) i

def splitOrigin (head : List T) : Origin args (past ++ [head]) t →
    Origin args past t ⊕ Port head t
  | .arg p => .inl (.arg p)
  | .output i p => (splitOutput head past i p).map (fun ⟨k, q⟩ => .output k q) id

/-- A typed substitution in one region, with the argument interface fixed. -/
abbrev Routing (args : List T) (source target : List (List T)) :=
  ∀ {t : T}, Origin args source t → Origin args target t

/-- Once a producer is kept, old wires follow the existing substitution and
its new result ports keep their positions in the new binding. -/
def Routing.push (route : Routing args past target) (head : List T) :
    Routing args (past ++ [head]) (target ++ [head]) :=
  fun wire => match splitOrigin head wire with
    | .inl prior => weaken head (route prior)
    | .inr port => newest port

def Routing.wires {ports : List T} (route : Routing args past target)
    (wires : Wires args past ports) : Wires args target ports :=
  wires.map (fun _ wire => route wire)

/-- Deleting a singleton binding replaces its result with a wire already
available in the preceding scope. -/
def dropNewest (replacement : Origin args past t) : Routing args (past ++ [[t]]) past :=
  fun wire => match splitOrigin [t] wire with
    | .inl prior => prior
    | .inr .head => replacement
    | .inr (.tail port) => nomatch port

end Scope

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs target : List (List (Ty Data))}
variable {out : ValueSort Data} {flow : Dataflow Op args past sigs}

/-- The substitution preserves the read at every wire of its source scope. -/
def Routing.Agrees (route : Routing args past target) (m : Model.{u,v,w} Op)
    (entry : Tuple (Val m.value) args) (old : Locals (Val m.value) past)
    (new : Locals (Val m.value) target) : Prop :=
  ∀ (t : Ty Data) (wire : Origin args past t),
    Diamond.read m wire entry old = Diamond.read m (route wire) entry new

/-- The exact scope in which the candidate's operands are read. -/
def operandScope :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → Producer flow out → List (List (Ty Data))
  | scope, _, _, _, .here => scope
  | _, _, _, _, .later ref => operandScope ref

/-- Reinterpret a predecessor wire in the original final scope, retaining its
original vertex number. -/
def inFinal {t : Ty Data} :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → (candidate : Producer flow out) →
      Origin args (operandScope candidate) t → Origin args (extend past sigs) t
  | scope, _, _, out, .here (rest := rest), wire =>
    keepOrigin (past := scope ++ [[.value out]]) rest (weaken [.value out] wire)
  | scope, _, _, _, .later (out := head) ref, wire =>
    inFinal (past := scope ++ [[.value head]]) ref wire

/-- Substitute operands throughout a surviving suffix and extend the
substitution at each binding. Output signatures are unchanged. -/
def routeSuffix :
    {past sigs target : List (List (Ty Data))} → (flow : Dataflow Op args past sigs) →
      Routing args past target →
      Dataflow Op args target sigs × Routing args (extend past sigs) (extend target sigs)
  | _, _, _, .nil, route => (.nil, route)
  | scope, _, target, .cons (out := out) op operands rest, route =>
    let suffix := routeSuffix (past := scope ++ [[.value out]]) (target := target ++ [[.value out]])
      rest (route.push [.value out])
    (.cons op (route.wires operands) suffix.1, suffix.2)

structure Rewrite (Op : Signature.{u,v} Data) (args : List (Ty Data))
    (past sigs : List (List (Ty Data))) where
  sigs' : List (List (Ty Data))
  flow : Dataflow Op args past sigs'
  route : Routing args (extend past sigs) (extend past sigs')

/-- The typed deletion. Legality of the substitution is checked by
`eliminate?` before using the resulting table as a verified rewrite. -/
def erase :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → (candidate : Producer flow out) →
      Origin args (operandScope candidate) (.value out) → Rewrite Op args past sigs
  | scope, _, _, out, .here (rest := rest), replacement =>
    let suffix := routeSuffix (past := scope ++ [[.value out]]) (target := scope)
      rest (dropNewest replacement)
    ⟨_, suffix.1, suffix.2⟩
  | _, _, _, _, .later (op := op) (inputs := operands) ref, replacement =>
    let suffix := erase ref replacement
    ⟨_, .cons op operands suffix.flow, suffix.route⟩

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- Delete only after the existing GVN check accepts and the supplied
prefix wire is the certified representative's wire. -/
def eliminate? (candidate representative : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out)) : Option (Rewrite Op args past sigs) :=
  if checkRepresentative candidate representative &&
      decide ((inFinal candidate replacement).address = representative.origin.address) then
    some (erase candidate replacement)
  else none

end Silmaril.SSA.SeaOfNodes.GVN.Elimination
