module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Environment.Defs

/-! # Request-free rows in mixed tables

## Mixed tables

A `MixRow` is a row of the environment fragment, which starts with a
request, or a request-free row `pure e`, whose program takes exit `e`
with its entry state and sends nothing. The routing of that exit on the
entry Bit is the row's action: a returned Bit, or a repeat to a row with
a Bit. `mixWritten row act` is the table as written. `mixRouter row act`
routes the unused exit of each request-free row like the used one.

## Silent states

On the split states of #5273, `mixSil row act x` is the action of a
request-free row entered with the Bit of its split state, and `none` at a
request row. `resolveN sil n a` follows at most `n` silent states from an
action. `Act.Settled sil a` says that `a` returns or repeats to a state
that sends a request. `Router.resolved t sil n` resolves every action of
a table.

`Ranked row act rank fuel` is the guard. The ranking is on rows with
their entry Bit. Only edges out of request-free rows are ranked, at the
Bit they are taken with, and only when they lead to a request-free row.
A silent cycle has no ranking.

## Landings

A `Landing` is where a loop entered with a constant ends up before its
first request: `ret c`, a Bit returned with no request, or `at t x q`, a
table of literal request trees entered at `x` with the constant `q`.
`Landed r L` says that `r` entered with each constant `q` is the landing
`L q`, in the opt-in quotient. `Landing.Rel` compares two landings.

`mixSource` is the table of literal request trees of the request rows at
their split states, with every action resolved. A request-free row is
replaced there by `idleRow`, which no resolved action reaches.
`mixLanding row act fuel j q` is the landing of row `j` entered with `q`,
and `mixCase` enters the two landings of a row by a case on the original
state.

## Regression tables

`hopRow` has two request-free rows in front of a request row. With
`hopAct f s`, row zero repeats to row one with the Bit negated when `f`;
row one returns on `false` and repeats to the request row with the Bit
`s` on `true`. `spinRow` with `spinAct` is a silent cycle.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)


variable {K M : Nat}

/-! ## Mixed tables -/

/-- A row of a mixed table: a row of the environment fragment, or a row
that sends no request and takes exit `e` with its entry state. -/
inductive MixRow where
  | ask (r : EnvRow)
  | pure (e : Fin 2)

def MixRow.program : MixRow → Program
  | .ask r => r.program
  | .pure e => .ret e 0

/-- The actions a row can take. A request-free row takes the action of
its exit on its entry state, whatever the other exit is routed to. -/
def MixRow.act (K : Nat) : MixRow → (Bool → Bool → Act K) → Bool → Bool → Act K
  | .ask _, a => a
  | .pure e, a => fun _ g => a (exitBit e) g

/-- The table as written: each row's program with its routing. -/
def mixWritten (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K) : Router K :=
  ⟨fun i => (row i).program, act⟩

/-- The table with the unused exit of each request-free row routed like
the used one. -/
def mixRouter (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K) : Router K :=
  ⟨fun i => (row i).program, fun i => (row i).act K (act i)⟩

/-! ## Silent states and their resolution -/

/-- Follow at most `n` silent states. `sil y` is the action of a silent
state `y`, and `none` for a state that sends a request. -/
def resolveN (sil : Fin (M + 1) → Option (Act M)) : Nat → Act M → Act M
  | 0, a => a
  | _ + 1, .ret c => .ret c
  | n + 1, .go y q =>
    match sil y with
    | some A => resolveN sil n A
    | none => .go y q

/-- The action returns, or repeats to a state that sends a request. -/
def Act.Settled (sil : Fin (M + 1) → Option (Act M)) : Act M → Prop
  | .ret _ => True
  | .go y _ => sil y = none

/-- The table with every action resolved through its silent states. -/
def Router.resolved (t : Router M) (sil : Fin (M + 1) → Option (Act M)) (n : Nat) : Router M :=
  ⟨t.prog, fun x a b => resolveN sil n (t.act x a b)⟩

/-- A ranking of the silent states: each silent state is below the fuel,
and a silent state that repeats to a silent state goes down. -/
def SilentRanked (sil : Fin (M + 1) → Option (Act M)) (rank : Fin (M + 1) → Nat) (fuel : Nat) : Prop :=
  (∀ y, rank y < fuel) ∧
    ∀ y A, sil y = some A → ∀ z q, A = .go z q → ∀ B, sil z = some B → rank z < rank y

/-- The silent action of a split state: a request-free row entered with
the Bit of its split state. -/
def MixRow.silent (m : MixRow) (a : Bool → Bool → Act K) (g : Bool) : Option (Act (K + (K + 1))) :=
  match m with
  | .ask _ => none
  | .pure e => some (redirect (a (exitBit e) g))

def mixSil (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (x : Fin (K + (K + 1) + 1)) : Option (Act (K + (K + 1))) :=
  (row (splitRow x)).silent (act (splitRow x)) (splitBit x)

/-- A ranking on rows with their entry Bit: a request-free row that
repeats to a request-free row goes down. Only edges out of request-free
rows are ranked, at the Bit they are taken with. -/
def Ranked (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (rank : Fin (K + 1) → Bool → Nat) (fuel : Nat) : Prop :=
  (∀ i g, rank i g < fuel) ∧
    ∀ i g e, row i = .pure e → ∀ j q, act i (exitBit e) g = .go j q → ∀ e', row j = .pure e' →
      rank j q < rank i g

/-! ## The request rows as literal request trees -/

/-- A row that repeats on every reply. It stands in for a request-free
row, which no resolved action reaches. -/
def idleRow : EnvRow := ⟨false, .ret 1 0, .ret 1 0⟩

def MixRow.envRow : MixRow → EnvRow
  | .ask r => r
  | .pure _ => idleRow

/-- The resolved actions of a request row; a stand-in row repeats to
itself. -/
def MixRow.settledAct (m : MixRow) (sil : Fin (M + 1) → Option (Act M)) (fuel : Nat) (x : Fin (M + 1))
    (g : Bool) (a : Bool → Bool → Act M) (a' b' : Bool) : Act M :=
  match m with
  | .ask _ => resolveN sil fuel (a a' b')
  | .pure _ => .go x g

def mixAct (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K) (fuel : Nat)
    (x : Fin (K + (K + 1) + 1)) : Bool → Bool → Act (K + (K + 1)) :=
  (row (splitRow x)).settledAct (mixSil row act) fuel x (splitBit x)
    fun a b => redirect (act (splitRow x) a b)

/-- Rows of the fragment at states that carry the Bit `c`, as literal
request trees: state `x` has the trees of its row entered with `c x`. -/
def kidsTable (c : Fin (M + 1) → Bool) (rows : Fin (M + 1) → EnvRow)
    (act : Fin (M + 1) → Bool → Bool → Act M) : LTable M :=
  ⟨fun x => (rows x).label, fun x => (rows x).kids (act x) (c x)⟩

/-- The request rows of the mixed table at their split states, with every
action resolved. -/
def mixSource (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K) (fuel : Nat) :
    LTable (K + (K + 1)) :=
  kidsTable splitBit (fun x => (row (splitRow x)).envRow) (mixAct row act fuel)

/-! ## Landings -/

/-- Where a loop entered with a constant lands: a returned Bit with no
request, or a table of literal request trees entered with a constant. -/
inductive Landing (M : Nat) where
  | ret (c : Bool)
  | at (t : LTable M) (x : Fin (M + 1)) (q : Bool)

def Landing.region : Landing M → Region signature.Instr
  | .ret c => .br 0 (bitTm c)
  | .at t x q => constEntry q (t.entered x)

theorem Landing.region_typed (L : Landing M) : ValueBranches [Ty.unit] L.region [Bit] := by
  cases L with
  | ret c => exact .br rfl (bitTm_typed c)
  | «at» t x q => exact constEntry_typed q (t.entered_typed x)

/-- Two landings agree: the same returned Bit, or the same constant into
equal entered loops. -/
def Landing.Rel {M' : Nat} : Landing M → Landing M' → Prop
  | .ret c, .ret c' => c = c'
  | .at t x q, .at t' x' q' => q = q' ∧ Eqv false [State] (t.entered x) (t'.entered x') [Bit]
  | _, _ => False

def Act.landing (t : LTable M) : Act M → Landing M
  | .ret c => .ret c
  | .go y q => .at t y q

/-- `r` entered with each constant is its landing. -/
def Landed (r : Region signature.Instr) (L : Bool → Landing M) : Prop :=
  ∀ q, Eqv false [Ty.unit] (constEntry q r) (L q).region [Bit]

/-- Where row `j` of the mixed table lands when entered with `q`. -/
def mixLanding (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K) (fuel : Nat)
    (j : Fin (K + 1)) (q : Bool) : Landing (K + (K + 1)) :=
  (resolveN (mixSil row act) fuel (.go (splitIdx j q) q)).landing (mixSource row act fuel)

/-- The two landings of a row, entered by a case on the original state. -/
def mixCase (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K) (fuel : Nat)
    (j : Fin (K + 1)) : Region signature.Instr :=
  caseEntry (mixLanding row act fuel j false).region (mixLanding row act fuel j true).region

theorem mixCase_typed (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K) (fuel : Nat)
    (j : Fin (K + 1)) : ValueBranches [State] (mixCase row act fuel j) [Bit] :=
  caseEntry_typed (Landing.region_typed _) (Landing.region_typed _)

/-! ## Regression tables -/

/-- Two request-free rows in front of a request row. Row zero takes its
repeat exit and row one its return exit. -/
def hopRow (l : Bool) (i : Fin 3) : MixRow :=
  match i with
  | 0 => .pure 1
  | 1 => .pure 0
  | 2 => .ask ⟨l, .ret 0 0, .ret 1 0⟩

/-- Row zero repeats to row one, with the Bit negated when `f`. Row one
returns `true` on `false` and repeats to the request row with the Bit `s`
on `true`. The request row returns its reply or repeats to row zero. -/
def hopAct (f s : Bool) (i : Fin 3) (x g : Bool) : Act 2 :=
  match i, x, g with
  | 0, _, g => .go 1 (f != g)
  | 1, _, false => .ret true
  | 1, _, true => .go 2 s
  | 2, false, y => .ret y
  | 2, true, y => .go 0 y

def hopRank (i : Fin 3) (_ : Bool) : Nat :=
  match i with
  | 0 => 2
  | 1 => 1
  | 2 => 0

/-- One request-free row that repeats to itself: a silent cycle. -/
def spinRow (_ : Fin 1) : MixRow := .pure 1

def spinAct (_ : Fin 1) (_ g : Bool) : Act 0 := .go 0 g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
