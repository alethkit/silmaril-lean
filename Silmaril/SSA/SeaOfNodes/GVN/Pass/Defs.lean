module

public import Silmaril.SSA.SeaOfNodes.GVN.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Defs

/-! Repeated discovery and checked elimination in a pure acyclic producer table. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Pass

open Diamond (Dataflow Signature Ty ValueSort)
open RVSDG (Origin extend)
open Elimination (Rewrite Routing operandScope)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {out : ValueSort Data} {flow : Dataflow Op args past sigs}

/-- A candidate in the table, with its result sort. -/
abbrev Candidate (flow : Dataflow Op args past sigs) := Σ out, Producer flow out

/-- Every producer, in table order. -/
def candidates : {past sigs : List (List (Ty Data))} →
    (flow : Dataflow Op args past sigs) → List (Candidate flow)
  | _, _, .nil => []
  | scope, _, .cons (out := out) op inputs rest =>
    ⟨out, .here⟩ :: (candidates (past := scope ++ [[.value out]]) rest).map
      (fun ⟨sort, ref⟩ => ⟨sort, .later (op := op) (inputs := inputs) ref⟩)

/-- Carry an existing wire to the scope just before the candidate. -/
def before {t : Ty Data} :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → (candidate : Producer flow out) →
      Origin args past t → Origin args (operandScope candidate) t
  | _, _, _, _, .here, wire => wire
  | scope, _, _, _, .later (out := head) ref, wire =>
    before (past := scope ++ [[.value head]]) ref (weaken [.value head] wire)

/-- Resolve an earlier representative as a same-sort wire in the candidate's
operand scope. -/
def replacement? :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → (candidate : Producer flow out) →
      Producer flow out → Option (Origin args (operandScope candidate) (.value out))
  | _, _, _, _, .here, _ => none
  | scope, _, _, _, .later (out := head) ref, .here =>
    some (before (past := scope ++ [[.value head]]) ref (newest (past := scope) .head))
  | scope, _, _, _, .later (out := head) ref, .later prior =>
    replacement? (past := scope ++ [[.value head]]) ref prior

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

def eliminateCandidate? (candidate : Producer flow out) : Option (Rewrite Op args past sigs) :=
  match Discovery.findRepresentative? candidate with
  | none => none
  | some representative =>
    match replacement? candidate representative with
    | none => none
    | some wire => Elimination.eliminate? candidate representative wire

/-- Run the first applicable deletion. Both discovery and the deletion check
use the supplied current table. -/
def step? (flow : Dataflow Op args past sigs) : Option (Rewrite Op args past sigs) :=
  (candidates flow).findSome? (fun ⟨_, candidate⟩ => eliminateCandidate? candidate)

def NoDuplicate (flow : Dataflow Op args past sigs) : Prop :=
  ∀ (out : ValueSort Data) (candidate representative : Producer flow out),
    checkRepresentative candidate representative = false

structure Result (Op : Signature.{u,v} Data) (args : List (Ty Data))
    (past sigs : List (List (Ty Data))) where
  rewrite : Rewrite Op args past sigs
  deletions : Nat

def unchanged (flow : Dataflow Op args past sigs) : Result Op args past sigs :=
  ⟨⟨sigs, flow, fun wire => wire⟩, 0⟩

/-- Compose two rewrites in passage order so old wires keep their meanings. -/
def compose (first : Rewrite Op args past sigs) (second : Rewrite Op args past first.sigs') :
    Rewrite Op args past sigs :=
  ⟨second.sigs', second.flow, fun wire => second.route (first.route wire)⟩

/-- Each iteration either makes one deletion and spends one unit of fuel or
stops. Every recursive step recomputes matches in the shorter table. -/
def run : Nat → {sigs : List (List (Ty Data))} →
    (flow : Dataflow Op args past sigs) → Result Op args past sigs
  | 0, _, flow => unchanged flow
  | fuel + 1, _, flow =>
    match step? flow with
    | none => unchanged flow
    | some first =>
      let tail := run fuel first.flow
      ⟨compose first tail.rewrite, tail.deletions + 1⟩

/-- Allow as many deletions as there are bindings, plus a final search. -/
def normalize (flow : Dataflow Op args past sigs) : Result Op args past sigs :=
  run (sigs.length + 1) flow

end Silmaril.SSA.SeaOfNodes.GVN.Pass
