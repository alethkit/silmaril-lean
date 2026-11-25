# Nondeterministic printing with finite hangs

[CALCO 2019, article 13, §1.1, pp. 13:2–3][paper] takes all nonempty subsets
of `(A* × X) + A≤ω`. The terminal summand includes both finite hangs and
infinite printed output.

[HangTraces][traces] defines the carrier `Traces`. Its lawful monad uses
singleton return and trace-set sequencing by `bindSet`. A hang after any
finite word retains that word, checked by `finite_hang_prefix`.

`FiniteRun` and `InfiniteRun` describe arbitrary loop bodies. The finite
cases either return or reach an explicit terminal trace. An infinite
execution contributes exactly the letters at positions witnessed by some
finite prefix, as checked by `chunkAt_some`. Empty step words are allowed.
`silent_loop_hangs` checks the finite hang of a loop that emits no letters.
`runs_nonempty` and `iterate_fixpoint` give a total operator on nonempty
trace sets and its unfolding equation. `iterate_naturality` and
`iterate_uniformity` check preservation of result continuations and pure
state comparisons. Codiagonal remains open.

```sh
lake build --wfail +Silmaril.Papers.Calco2019.Examples.PrintingHangTraces
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[traces]: ../../Silmaril/Semantics/Calco2019/Examples/Printing/HangTraces/Thms.lean
