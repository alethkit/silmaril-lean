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

/-- Decode the physical binder after CFG entry has substituted its incoming
argument. The live scope is the newest-first list of typed Bit replies. -/
def readQuery (written : Bool) (n : Nat) : Tm signature.Instr → Option (Expr n)
  | .var j => if h : written = true ∧ j < n then some (.read ⟨j, h.2⟩) else none
  | a => (literalQuery a).map Expr.literal

/-- Each request uses a literal or a single live binder. The fixed-order
truth-table key is injective on these operands. -/
inductive Direct : {n : Nat} → Tree n → Prop
  | ret {n : Nat} (right : Bool) (i : Fin n) : Direct (.ret right i)
  | literal {n : Nat} (label b : Bool) {l r : Tree (n + 1)} :
      Direct l → Direct r → Direct (.ask label (.literal b) l r)
  | var {n : Nat} (label : Bool) (i : Fin n) {l r : Tree (n + 1)} :
      Direct l → Direct r → Direct (.ask label (.read i) l r)

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

/-- Follow tagged requests, typed variable returns and variable lets.
A table can leave directly at either outward exit, follow a local branch,
or use one-block entry substitution. Fuel bounds local unfolding. -/
def readWith (written : Bool) : Nat → (n : Nat) → Nat → Region signature.Instr → Option (Tree n)
  | 0, _, _, _ => none
  | _fuel + 1, n, offset, .br i (.var j) => do
    let slot ← if h : j < n then some (⟨j, h⟩ : Fin n) else none
    if i = offset then some (.ret false slot)
    else if i = offset + 1 then some (.ret true slot)
    else none
  | fuel + 1, n, offset, .case (.op (.ask label) arg) left right => do
    let query ← readQuery written n arg
    let l ← readWith written fuel (n + 1) offset left
    let r ← readWith written fuel (n + 1) offset right
    some (.ask label query l r)
  | fuel + 1, n, offset, .let₁ (.var j) body =>
    readWith written fuel n offset (body.substVars (Tm.singleSubst (.var j)))
  | fuel + 1, n, offset, .cfg entry k rows =>
    (readWith written fuel n (k + offset) entry).orElse fun _ =>
      (enter? k entry rows).bind (readWith written fuel n offset)
  | _, _, _, _ => none

abbrev read := readWith false

/-- The original outward region with its exact typing, before literal exit packing. -/
abbrev Candidate := {r : Region signature.Instr // ValueBranches [Bit] r Exits}

def Candidate.packed (p : Candidate) :=
  Paper.TypeCategory.ofRegion p.property.packExits

noncomputable def Candidate.observations (p : Candidate) (guard : Bool) : Set Observation :=
  ((denote.map ((Paper.Extension.Singleton.projection Seed).map p.packed)).of (bit guard)).outcomes

def Candidate.read (p : Candidate) (fuel : Nat) : Option (Tree 1) :=
  Readback.read fuel 1 0 p.val

/-- Read a forwarded variable directly; its selected syntax keeps the same
argument, including the payload hidden by the Boolean trace observation. -/
def Candidate.readWithVariables (p : Candidate) (fuel : Nat) : Option (Tree 1) :=
  readWith true fuel 1 0 p.val

/-- A table or constructor outside the recognized scope, or insufficient fuel,
is reported as unknown. A difference uses a reachable all-replies history. -/
inductive Verdict where
  | unknown
  | equal
  | different (witness : Difference)
deriving DecidableEq

def compareTrees : Option (Tree 1) → Option (Tree 1) → Verdict
  | some t, some u =>
    match t.separate? u with
    | none => .equal
    | some w => .different w
  | _, _ => .unknown

def compare (fuel : Nat) (p q : Candidate) : Verdict :=
  compareTrees (p.read fuel) (q.read fuel)

def compareWithVariables (fuel : Nat) (p q : Candidate) : Verdict :=
  compareTrees (p.readWithVariables fuel) (q.readWithVariables fuel)

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

namespace VariableExample

/-- Both tags share one written join. Only the second tag may pass the
original guard instead of the latest reply. The join's alias shifts its
incoming bit one binder before the second request reads it. -/
def shared (altered : Bool) (offset : Nat) : Region signature.Instr :=
  .cfg (.case (.op (.ask false) (literal false)) (.br 0 (.var 0))
      (.br 0 (.var (if altered then 1 else 0)))) 1
    (fun _ => .let₁ (.var 0) (.case (.op (.ask true) (.var 1))
      (.br (1 + (offset + 1)) (.var 0)) (.br (1 + (offset + 1)) (.var 0))))

def numbered (renumbered altered : Bool) : Region signature.Instr :=
  if renumbered then
    .cfg (.br 1 (.var 0)) 2 (Fin.cases (shared altered 2) (fun _ => .br 0 (.var 0)))
  else
    .cfg (.br 0 (.var 0)) 2 (Fin.cases (.br 1 (.var 0)) (fun _ => shared altered 2))

/-- This query itself makes a request. The recognizer leaves this syntax
unknown instead of duplicating, moving or interpreting its effects. -/
def effectfulQuery : Region signature.Instr :=
  call true (.case (.op (.ask false) (literal false)) (.var 0) (.var 0))

def next (slot : Fin 2) : Tree 2 :=
  .ask true (.read slot) (.ret true 0) (.ret true 0)

def querySlot (altered tag : Bool) : Fin 2 := if altered && tag then 1 else 0

def expected (altered : Bool) : Tree 1 :=
  .ask false (.literal false) (next (querySlot altered false)) (next (querySlot altered true))

def witness : Difference :=
  ⟨false, false, ⟨[event false false (true, true), event true true (false, false)], true, false⟩⟩

end VariableExample

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback
