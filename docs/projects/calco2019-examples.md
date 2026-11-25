# Coverage of the numbered CALCO 2019 examples

Paul Blain Levy and Sergey Goncharov,
[*Coinductive Resumption Monads: Guarded Iterative and Guarded Elgot*][paper],
CALCO 2019, article 13, pp. 13:1–13:17. The published PDF has SHA-256
`e9617e110c12a9ab2e99de57c75b2a23ed9191f6721afe92c0bba6a8b7ecb3ab`.
The numbered examples are 10 (p. 13:8), 20 (pp. 13:10–11), and 22
(pp. 13:11–12).

| Paper | Lean modules | Checked claims and scope |
| --- | --- | --- |
| 10(1), 20(1) | [SetModels][sets] | `Trunc` is inhabited exactly when the underlying type is inhabited. The concrete arrow is guarded in each summand and fails the guard for their union. The CALCO least guard gives unique fixpoints via `trunc_iterative`. |
| 10(2), 20(2) | [SetModels][sets] | `powersetElgot` instantiates the CALCO Elgot interface. `powerset_least` proves leastness and `nonemptyIter` proves closure under restriction for bodies with a direct return at every state. Membership is the library's predicate for a finite successful run. The categorical guarded Elgot bundle for the nonempty subtype remains open here. |
| 10(3), 20(3) | [Probability coverage][prob] | The published transition probabilities give eventual return mass `2/3`. The proposed normalization fails the fixpoint equation. There is a general unnormalized least solution for PMF bodies and an obstruction to natural, uniform PMF-valued iteration with the printed guard. |
| 10(4), 20(4) | [Printing][printing] | The all-recursive one-letter writer is guarded and has no finite-word fixpoint. Collapsing divergence to a singleton gives a fixpoint for the witness. The general writer extensions by left actions and their iteration laws remain open here. |
| 10(5), 20(5) | [Printing][printing] | The finite-plus-infinite trace model checks the guard and the one-letter separating equation. Its finite-only and productive sets are nonempty, distinct fixpoints, ordered by inclusion. The no-output self-loop is unguarded. The general three-clause trace iteration and Conway laws remain open here. |
| 22 | [Exceptions][exceptions] | For a total Elgot base on types and the identity parameter functor, `resultSum` identifies the exception carrier with the paper's sum, `fibre` gives each CALCO Elgot monad. `ExceptT.adapt` preserves pure, bind, and iteration and defines the maps of the `parametrized` guarded Elgot functor. The abstract parametrized construction with an arbitrary guard and endofunctor is outside this example slice. |

The accounts of printing, I/O, and free extensions in the paper's introduction
are unnumbered. The table covers the three numbered examples.

## Checking

```sh
lake build --wfail \
  +Silmaril.Papers.Calco2019.Examples.SetModels \
  +Silmaril.Papers.Calco2019.Examples.Printing \
  +Silmaril.Papers.Calco2019.Examples.Exceptions
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[sets]: ../../Silmaril/Semantics/Calco2019/Examples/SetModels/Thms.lean
[printing]: ../../Silmaril/Semantics/Calco2019/Examples/Printing/Thms.lean
[exceptions]: ../../Silmaril/Semantics/Calco2019/Examples/Exceptions/Thms.lean
[prob]: calco2019-examples-probability.md
