module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Compile.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CompositeTables

/-! # A two-request program written as one step: the conditional lift

No seed is added. Nothing here is inferred from a model.

## What is proved

* `chain_routerRoute` (default Paper): the chain into `p₂` followed by a
  routing `a` is the routing whose return leaves send the request of
  `p₂` with the returned Bit as query, and whose repeat leaves take the
  actions of `a`. It uses the case analysis of the Bit sum and no rule
  beyond the category of default Paper.
* `duoRouter_eqv_source`: **if** the written step of every row factors
  (`StepFactors`), the table whose rows are the two-request programs
  `duoProgram` equals, at every entry, the table of literal request
  trees `duoSource`. The lift goes through the rows in the quotient and
  the dispatcher and feedback of the literal loops.
* `duoRouter_eqv_iff_valid`: under the same hypothesis for two such
  tables, equality at given entries is validity in every supported
  model, by `LTable.eqv_iff_valid`.

## What is not proved: the next lemma

`StepFactors (duoProgram l₁ l₂) (labelPoll l₁).program (labelPoll l₂).program`,
that is

  `Eqv (stepRegion (duoProgram l₁ l₂)) (chainedStep … …)`.

The two regions differ as follows. In the written program the second
request stands directly in the left reply arm of the first. In the
chained step the first program ends by branching with its packed result,
and the chain then cases on that result. After label substitution the
chained step has a case on a constructor in each reply arm, under the
first request.

Default Paper's rules are the CFG rules, product β and η, the
congruences, label and variable substitution, label renaming, collapse
and uniformity. None of them is a rule for a case on a constructor, so
this file does not attempt the equation in default Paper. In the opt-in
quotients it would have to come from the administrative-return and
case-bind seeds, through a lemma that reduces such a case under a
request. That lemma is not derived here, and the equation has not been
checked in a model here.

## Scope

The representative program has a second request that is selected by the
first reply's tag and queried with the first reply's payload; its results
are the second reply's or the first reply's payload. A leaf that returns a
captured Bit after the second request is not covered: the chain would
have to carry that Bit. No compositional statement for the whole grammar
of written programs is made, and nothing is claimed about packed
dispatchers in general.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K₁ K₂ : Nat}

/-- The chain into `p₂` followed by the routing `a`, in default Paper. -/
theorem chain_routerRoute (K : Nat) (p₂ : Program) (a : Bool → Bool → Act K) :
    ofRegion (chain_typed p₂) ≫ ofRegion (routerRoute_typed K a) =
      ofRegion (genRoute_typed fun x y => treeRegion_typed K (duoKids K p₂ a x y)) :=
  Tables.chain_route K p₂ a

/-- If every written step factors, the table of two-request programs
equals the table of literal request trees at every entry. -/
theorem duoRouter_eqv_source (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (fac : ∀ i, StepFactors (duoProgram (l₁ i) (l₂ i)) (labelPoll (l₁ i)).program (labelPoll (l₂ i)).program)
    (j : Fin (K + 1)) :
    Eqv false [State] ((duoRouter l₁ l₂ act).entered j) ((duoSource l₁ l₂ act).entered j) [Bit] :=
  Tables.duo_table_eqv l₁ l₂ act fac j

/-- Under that hypothesis, two such tables are equal at given entries
exactly when they are valid in every supported model. -/
theorem duoRouter_eqv_iff_valid (l₁ l₂ : Fin (K₁ + 1) → Bool) (act : Fin (K₁ + 1) → Bool → Bool → Act K₁)
    (m₁ m₂ : Fin (K₂ + 1) → Bool) (act' : Fin (K₂ + 1) → Bool → Bool → Act K₂)
    (fac : ∀ i, StepFactors (duoProgram (l₁ i) (l₂ i)) (labelPoll (l₁ i)).program (labelPoll (l₂ i)).program)
    (fac' : ∀ i, StepFactors (duoProgram (m₁ i) (m₂ i)) (labelPoll (m₁ i)).program (labelPoll (m₂ i)).program)
    (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((duoRouter l₁ l₂ act).entered i₁) ((duoRouter m₁ m₂ act').entered i₂) [Bit] ↔
      Valid ((duoRouter l₁ l₂ act).entered_typed i₁).hasType
        ((duoRouter m₁ m₂ act').entered_typed i₂).hasType :=
  ⟨fun e => valid_of_eqv false e _ _,
    fun v => (duoRouter_eqv_source l₁ l₂ act fac i₁).trans
      (((LTable.eqv_iff_valid (duoSource l₁ l₂ act) (duoSource m₁ m₂ act') i₁ i₂).2
        (Valid.trans (Valid.symm (valid_of_eqv false (duoRouter_eqv_source l₁ l₂ act fac i₁) _ _))
          (Valid.trans v (valid_of_eqv false (duoRouter_eqv_source m₁ m₂ act' fac' i₂) _ _)))).trans
        (duoRouter_eqv_source m₁ m₂ act' fac' i₂).symm)⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
