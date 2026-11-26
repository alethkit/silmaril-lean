module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Default.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Reflection.Defs

/-! # Read back a typed outward Bit region as a selected request tree -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr)

abbrev Live (n : Nat) := List.replicate n Bit

def slots (n : Nat) : Slots (Live n) n where
  index := Fin.val
  typed i := by simp [At, Live, i.isLt]
  distinct := Fin.val_injective

def literalQuery : Tm signature.Instr → Option Bool
  | .inl .unit => some false
  | .inr .unit => some true
  | _ => none

def forwarding : Region signature.Instr → Option (Nat × Nat)
  | .br i (.var j) => some (i, j)
  | _ => none

/-- At multi-block arities, enter a written local branch with a variable
argument. A one-block table additionally admits literal entry substitution. -/
def enter? (k : Nat) (entry : Region signature.Instr) (rows : Fin k → Region signature.Instr) :
    Option (Region signature.Instr) :=
  match forwarding entry with
  | some (i, j) =>
    if hi : i < k then
      some (.cfg ((rows ⟨i, hi⟩).substVars (Tm.singleSubst (.var j))) k rows)
    else none
  | none =>
    if hk : k = 1 then some (entry.lsubst (cfgEntryContinuations (hk ▸ rows))) else none

/-- Follow literal tagged requests, typed variable returns and variable lets.
A table can leave directly at either outward exit, follow a local branch,
or use one-block entry substitution. Fuel bounds local unfolding. -/
def read : Nat → (n : Nat) → Nat → Region signature.Instr → Option (Tree n)
  | 0, _, _, _ => none
  | _fuel + 1, n, offset, .br i (.var j) => do
    let slot ← if h : j < n then some (⟨j, h⟩ : Fin n) else none
    if i = offset then some (.ret false slot)
    else if i = offset + 1 then some (.ret true slot)
    else none
  | fuel + 1, n, offset, .case (.op (.ask label) arg) left right => do
    let query ← literalQuery arg
    let l ← read fuel (n + 1) offset left
    let r ← read fuel (n + 1) offset right
    some (.ask label (.literal query) l r)
  | fuel + 1, n, offset, .let₁ (.var j) body =>
    read fuel n offset (body.substVars (Tm.singleSubst (.var j)))
  | fuel + 1, n, offset, .cfg entry k rows =>
    (read fuel n (k + offset) entry).orElse fun _ =>
      (enter? k entry rows).bind (read fuel n offset)
  | _, _, _, _ => none

/-- The original outward region with its exact typing, before literal exit packing. -/
abbrev Candidate := {r : Region signature.Instr // ValueBranches [Bit] r Exits}

def Candidate.packed (p : Candidate) :=
  Paper.TypeCategory.ofRegion p.property.packExits

noncomputable def Candidate.observations (p : Candidate) (guard : Bool) : Set Observation :=
  ((denote.map ((Paper.Extension.Singleton.projection Seed).map p.packed)).of (bit guard)).outcomes

def Candidate.read (p : Candidate) (fuel : Nat) : Option (Tree 1) :=
  Readback.read fuel 1 0 p.val

/-- A table or constructor outside the recognized scope, or insufficient fuel,
is reported as unknown. A difference uses a reachable all-replies history. -/
inductive Verdict where
  | unknown
  | equal
  | different (witness : Difference)
deriving DecidableEq

def compare (fuel : Nat) (p q : Candidate) : Verdict :=
  match p.read fuel, q.read fuel with
  | some t, some u =>
    match t.separate? u with
    | none => .equal
    | some w => .different w
  | _, _ => .unknown

namespace Example

/-- Both reply tags transfer their actual payload to the same written block. -/
def joined (right : Bool) (offset : Nat) : Region signature.Instr :=
  .cfg (.case (.op (.ask false) (literal false)) (.br 0 (.var 0)) (.br 0 (.var 0))) 1
    (fun _ => .br (1 + (offset + if right then 1 else 0)) (.var 0))

/-- The first layout enters zero and forwards to one. -/
def forward (right : Bool) : Region signature.Instr :=
  .cfg (.br 0 (.var 0)) 2 (Fin.cases (.br 1 (.var 0)) (fun _ => joined right 2))

/-- This layout enters one and forwards to zero. -/
def backward (right : Bool) : Region signature.Instr :=
  .cfg (.br 1 (.var 0)) 2 (Fin.cases (joined right 2) (fun _ => .br 0 (.var 0)))

/-- This well-typed request has a live variable query outside this readback. -/
def variableQuery : Region signature.Instr := call false (.var 0)

def expected (right : Bool) : Tree 1 :=
  .ask false (.literal false) (.ret right 0) (.ret right 0)

def witness : Difference := ⟨false, false, ⟨[event false false (false, false)], false, false⟩⟩

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback
