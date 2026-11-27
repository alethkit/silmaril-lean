module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Environment.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentRegression

/-! # Request-free rows in mixed tables, at the original entries

A mixed table has rows that start with a request and rows that send no
request. No seed is added. Nothing here is inferred from a model.

## The guard

`Ranked row act rank fuel` ranks the edges out of request-free rows, on
rows with their entry Bit. A finite forwarding chain has a ranking. A
silent cycle has none (`spin_not_ranked`), and nothing is proved about
it. With a ranking every action settles within the fuel: it reaches a
return or a request row (`resolveN_settled`). The elimination below is
stated for settled actions.

## Default Paper: the elimination over ranked silent paths

These are equations of arrows of default Paper. They use no opt-in rule.

* `pureRow_const`: a request-free row entered with a constant is the
  action of its exit on that constant.
* `Router.resolved_arrow`: the reusable elimination lemma. Let `sil` give
  the action of each silent state of a router table when entered with the
  Bit `c` assigns to it. If all repeats carry the Bit of their target and
  every action is settled after `n` silent steps, then the table and the
  table with every action resolved have the same entered loop at every
  state. The proof runs the silent states in an inner loop and uses the
  fixpoint and codiagonal laws of iteration, by induction on the fuel.
* `mixWritten_arrow_mixRouter`: the table as written and the table with
  the unused exit of each request-free row rerouted have the same entered
  loops.

## The opt-in quotient: the original entries

* `mixRouter_landed`, `mixWritten_landed`: with a ranking, row `j`
  entered with the constant `q` is `mixLanding row act fuel j q`: a Bit
  returned with no request when the silent path from `(j, q)` reaches a
  return, and otherwise the table of literal request trees entered at the
  request row the path reaches, with the Bit it arrives with. Entries at
  request-free rows are included.
* `mixWritten_eqv_mixCase`: on an arbitrary state, the table entered at
  `j` is its two landings entered by a case on that state.

The steps are the split-state fold of #5273, the elimination above, a
bisimulation that drops the request-free rows no resolved action reaches,
and the specialization of #5277 at the request rows.

## The opt-in quotient: completeness

* `Landed.eqv_iff_rel`: two loops with landings are equal exactly when
  their landings agree at each constant.
* `Landed.complete`: exactly when they are valid in every supported
  model. The converse reads the request-prefix model: a return and a
  pending request are told apart, a request shows its query, and literal
  request trees are determined at one constant entry.
* `Pointed.landed`: the loops of the earlier files have landings.
* `mixWritten_complete`, `mixWritten_eqv_ltable_iff_valid`: the instances
  for ranked mixed tables at their original entries.

These depend on phase uniformity, unit η and the request-prefix model.
They are not statements about default Paper.

## Regression

`hopRow` with `hopAct f s` has two request-free rows before a request
row, and a ranking (`hop_ranked`).

* `hop_return`: entered with `true`, two silent hops reach a return.
* `hop_request`: entered with `false`, two silent hops change the Bit and
  reach the request row with `true`.
* `hop_eqv_iff`: two such tables are equal at the first row exactly when
  the hop changes the Bit in the same way and the request row is entered
  with the same Bit.

## Scope

Silent cycles are out of scope. The request rows are rows of the
environment fragment. Nothing is claimed for packed dispatchers in
general, and no completeness is claimed for default Paper.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity


variable {K K₁ K₂ M M' : Nat}

/-! ## The guard -/

/-- With a ranking, the fuel resolves every action. -/
theorem resolveN_settled {row : Fin (K + 1) → MixRow} {act : Fin (K + 1) → Bool → Bool → Act K}
    {rank : Fin (K + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel) (a : Act (K + (K + 1))) :
    (resolveN (mixSil row act) fuel a).Settled (mixSil row act) :=
  Tables.mix_settled row act hr a

/-- A silent cycle has no ranking. -/
theorem spin_not_ranked (rank : Fin 1 → Bool → Nat) (fuel : Nat) : ¬ Ranked spinRow spinAct rank fuel :=
  Tables.spin_not_ranked rank fuel

/-! ## Default Paper: the elimination over ranked silent paths -/

/-- A request-free row entered with a constant is the action of its exit
on that constant. -/
theorem pureRow_const (M : Nat) (e : Fin 2) (a : Bool → Bool → Act M) (g : Bool) :
    ofRegion (seqValueBranches (const_typed g) (routerRow_typed M (.ret e 0) a)) =
      ofRegion (act_typed M (a (exitBit e) g)) :=
  Tables.pure_const M e a g

/-- A table and the table with every action resolved through its silent
states have the same entered loops, in default Paper. -/
theorem Router.resolved_arrow (t : Router M) (c : Fin (M + 1) → Bool) (sil : Fin (M + 1) → Option (Act M))
    (n : Nat)
    (hsil : ∀ y A, sil y = some A →
      ofRegion (seqValueBranches (const_typed (c y)) (t.rows_typed y)) = ofRegion (act_typed M A))
    (hcar : ∀ y A, sil y = some A → A.Carries c) (hact : ∀ x a b, (t.act x a b).Carries c)
    (hset : ∀ x a b, (resolveN sil n (t.act x a b)).Settled sil) (x : Fin (M + 1)) :
    ofRegion ((t.resolved sil n).entered_typed x) = ofRegion (t.entered_typed x) :=
  Tables.silent_entered t c sil n hsil hcar hact hset x

/-- The table as written and the table with the unused exits rerouted
have the same entered loops, in default Paper. -/
theorem mixWritten_arrow_mixRouter (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    ofRegion ((mixWritten row act).entered_typed j) = ofRegion ((mixRouter row act).entered_typed j) :=
  Tables.mix_written_arrow row act j

/-! ## The opt-in quotient: the original entries -/

section Entries

variable {row : Fin (K + 1) → MixRow} {act : Fin (K + 1) → Bool → Bool → Act K}
  {rank : Fin (K + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel)

include hr in
/-- A ranked mixed table entered with each constant is its landing. -/
theorem mixRouter_landed (j : Fin (K + 1)) :
    Landed ((mixRouter row act).entered j) (mixLanding row act fuel j) :=
  Tables.mix_landed row act hr j

include hr in
/-- The same for the table as written. -/
theorem mixWritten_landed (j : Fin (K + 1)) :
    Landed ((mixWritten row act).entered j) (mixLanding row act fuel j) :=
  Tables.written_landed row act hr j

include hr in
/-- On an arbitrary state, the table is its two landings entered by a
case on that state. -/
theorem mixWritten_eqv_mixCase (j : Fin (K + 1)) :
    Eqv false [State] ((mixWritten row act).entered j) (mixCase row act fuel j) [Bit] :=
  Tables.written_case row act hr j

end Entries

/-! ## The opt-in quotient: completeness -/

section Complete

variable {r r' : Region signature.Instr} {L : Bool → Landing M} {L' : Bool → Landing M'}

/-- Loops with landings are equal exactly when their landings agree at
each constant. -/
theorem Landed.eqv_iff_rel (hl : Landed r L) (hl' : Landed r' L') (h : ValueBranches [State] r [Bit])
    (h' : ValueBranches [State] r' [Bit]) : Eqv false [State] r r' [Bit] ↔ ∀ q, (L q).Rel (L' q) :=
  Tables.landed_iff_rel h h' hl hl'

/-- And exactly when they are valid in every supported model. -/
theorem Landed.complete (hl : Landed r L) (hl' : Landed r' L') (h : ValueBranches [State] r [Bit])
    (h' : ValueBranches [State] r' [Bit]) : Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  Tables.landed_complete h h' hl hl'

end Complete

/-- A loop that is literal request trees at each constant lands in them. -/
theorem Pointed.landed {r : Region signature.Instr} {t : Bool → LTable M} {x : Bool → Fin (M + 1)}
    (hp : Pointed r t x) : Landed r fun q => .at (t q) (x q) q :=
  Tables.landed_of_pointed hp

/-- Two ranked mixed tables are equal at given original entries exactly
when they are valid in every supported model. -/
theorem mixWritten_complete {row : Fin (K₁ + 1) → MixRow} {act : Fin (K₁ + 1) → Bool → Bool → Act K₁}
    {rank : Fin (K₁ + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel)
    {row' : Fin (K₂ + 1) → MixRow} {act' : Fin (K₂ + 1) → Bool → Bool → Act K₂}
    {rank' : Fin (K₂ + 1) → Bool → Nat} {fuel' : Nat} (hr' : Ranked row' act' rank' fuel')
    (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((mixWritten row act).entered i₁) ((mixWritten row' act').entered i₂) [Bit] ↔
      Valid ((mixWritten row act).entered_typed i₁).hasType ((mixWritten row' act').entered_typed i₂).hasType :=
  (mixWritten_landed hr i₁).complete (mixWritten_landed hr' i₂) ((mixWritten row act).entered_typed i₁)
    ((mixWritten row' act').entered_typed i₂)

/-- The same against any table of literal request trees. -/
theorem mixWritten_eqv_ltable_iff_valid {row : Fin (K₁ + 1) → MixRow}
    {act : Fin (K₁ + 1) → Bool → Bool → Act K₁} {rank : Fin (K₁ + 1) → Bool → Nat} {fuel : Nat}
    (hr : Ranked row act rank fuel) (s : LTable K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((mixWritten row act).entered i₁) (s.entered i₂) [Bit] ↔
      Valid ((mixWritten row act).entered_typed i₁).hasType (s.entered_typed i₂).hasType :=
  (mixWritten_landed hr i₁).complete
    (LTable.pointed_of_eqv (s.entered_typed i₂) s i₂
      (Paper.Extension.Eqv.refl (s.entered_typed i₂).hasType)).landed
    ((mixWritten row act).entered_typed i₁) (s.entered_typed i₂)

/-! ## Regression -/

theorem hop_ranked (l f s : Bool) : Ranked (hopRow l) (hopAct f s) hopRank 3 :=
  Tables.hop_ranked l f s

/-- Entered with `true`, two silent hops reach a return. -/
theorem hop_return (l : Bool) : mixLanding (hopRow l) (hopAct true true) 3 0 true = .ret true :=
  Tables.hop_return l

/-- Entered with `false`, two silent hops change the Bit and reach the
request row with `true`. -/
theorem hop_request (l : Bool) :
    mixLanding (hopRow l) (hopAct true true) 3 0 false =
      .at (mixSource (hopRow l) (hopAct true true) 3) (splitIdx 2 true) true :=
  Tables.hop_request l

/-- Two tables are equal at the first row exactly when the hop changes
the Bit in the same way and the request row is entered with the same Bit. -/
theorem hop_eqv_iff (l f s f' s' : Bool) :
    Eqv false [State] ((mixWritten (hopRow l) (hopAct f s)).entered 0)
      ((mixWritten (hopRow l) (hopAct f' s')).entered 0) [Bit] ↔ f = f' ∧ s = s' :=
  Tables.hop_eqv_iff l f s f' s'

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
