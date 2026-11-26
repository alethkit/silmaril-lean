# Bare and bind-first LambdaSSA iteration

The ordered-pair singleton quotient with branch binding implements exact-sum
iteration by forming `iterateRegion A r.bindBranchArguments` and taking its
class. This operation accepts any exactly typed step `r : [A] → [B ⊕ A]`.
The left reply returns a result and the right reply supplies the next state.
[Iteration API](../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/WithProjectionReturnsAndUnitEta/WithBranchBinding/OrderedPairSingleton/Iteration/Thms.lean)

The bare operation `iterateRegion A r` also typechecks. At a raw branch,
substituting the iteration dispatcher can place the branch argument directly
in a case scrutinee. Binding first keeps that computation in a unary let
and dispatches on the bound sum. The opt-in branch-binding rule equates
the two input steps. It does not equate the resulting bare loops.

The regression uses `br 0 (op poll (var 0))`, where the reply may select
either return or repeat. A syntax transformation retags the head primitive
of a region-case scrutinee to `query`. It preserves typing and the entire
ordered-pair branch-binding rewrite relation, including the guarded
substitutions in the CFG rules. In the transformed syntax, the standard
typed weak ITree interpretation observes `query` first in the bare feedback
CFG and `poll` first in the bind-first CFG. The regression proves
`bare_iterate_not_congruent` and checks the inequality against the installed
quotient operation in `bare_iterate_ne_iterateSum`.
[Regression API](../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/WithProjectionReturnsAndUnitEta/WithBranchBinding/OrderedPairSingleton/Iteration/Bare/Thms.lean)

For any step with `ValueBranches`, including arbitrary captures,
`guarded_bare_eq_bound` proves agreement in `Paper.Eqv`. Both presentations
use the same exact label dispatcher. The guard lets the proof postsubstitute
that dispatcher through the branch normalization rewrite.
[Guarded agreement](../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/WithProjectionReturnsAndUnitEta/WithBranchBinding/OrderedPairSingleton/Iteration/Thms.lean)

The arbitrary-scrutinee conversion has an independent denotational proof
under the coherent strong Elgot Freyd assumptions of `denote_dispatch_bind`.
Its endpoints are already guarded in the separating fixture, so adding it
as a rewrite would identify additional guarded classes. The observer's
separation concerns the rewrite relation. Ordinary denotation agrees on the untransformed case
and let.
[Model hypotheses and separation](../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/WithProjectionReturnsAndUnitEta/WithBranchBinding/OrderedPairSingleton/Iteration/Bare/Thms.lean)

From the repository root, the warning-as-error build checks the proof,
the fixture, and its comparison to the installed quotient operator.

```sh
lake build --wfail +Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Bare.Thms
```
