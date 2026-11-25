# Concrete models in the CALCO 2019 introduction

[Levy and Goncharov, CALCO 2019, article 13][paper], §§1.1–1.3, pp. 13:2–5.
See the [numbered examples][examples] for Examples 10, 20, and 22.

| Source | Concrete model and coverage |
| --- | --- |
| §1.1, pp. 13:2–3 | The finite-word and productive printing monads are covered under Examples 10(4–5) and 20(4–5). [Hangs][hangs] checks the deterministic complete Elgot model which retains the finite output of a hanging computation. The nondeterministic hang model uses sets of these traces. |
| §1.2, pp. 13:3–4 | The paper specifies initial and final coalgebras for deterministic printing, and uses the countable nonempty powerset for printing and general signature I/O. The unrestricted nonempty trace powerset in Example 20(5) does not impose the countable branching condition of these resumption instances. |
| §1.3, p. 13:5 | [Delay][delay] checks the identity-base, identity-operation case with Mathlib's raw `Computation` type, which keeps every explicit delay. |

## Deterministic printing with finite hangs

`Hangs.Model` has carrier `(List A × X) ⊕ Stream'.Seq A`. The successful
summand records a finite word and return value. The terminal summand
records either a finite sequence that ends with a hang or an infinite
stream of characters.

`unfoldTrace_return` checks the successful case. `unfoldTrace_spec` and
`unfoldTrace_unique` prove finality for the letter-by-letter observation
`Maybe (X + A × -)`. The actual CALCO parameter construction uses the
classical equivalence `Part.equivOption` for the Maybe layer.
`unit_eq` and `extend_eq` identify the resulting monad operations.
`isElgot` applies the resumption theorem to the total Elgot base `Part`.

```sh
lake build --wfail +Silmaril.Papers.Calco2019.Examples.PrintingHangs
```

## Finite and productive deterministic words

`WordResumptions` checks the other two carrier identifications
on p. 13:3. `initial` uses the empty-word return and letter prepend to show
that `List A × X` is the initial algebra of `X + A × -`.
`terminal` uses the head of the stream to make `(List A × X) ⊕ (ℕ → A)`
the final coalgebra of the same functor. The productive coalgebra embeds in
the hang coalgebra, and unfolding a total printing layer stays in the
productive carrier. [Lean declarations](../../Silmaril/Semantics/Calco2019/Examples/Printing/WordResumptions/Thms.lean)

## Capretta delay

`Delay.coalgebra` observes a return or a single further delay.
`terminal` proves finality by the strong bisimulation principle for
`Computation`. `resumptions` supplies the chosen final coalgebras of the
actual CALCO parameter family. `obj_eq` and `out_eq` identify the carrier
and destructor. `unit_eq` and `extend_eq` identify the resumption monad's
return and Kleisli extension with `Computation.pure` and `Computation.bind`.
`free` specializes the CALCO free guarded Elgot object theorem.

The citation to Capretta [5] identifies the underlying coinductive
datatype for intensional partiality. The Lean instance checks the raw
delay monad on types. The interpretation of general recursion in an
intensional type theory is Capretta's external result.

```sh
lake build --wfail +Silmaril.Papers.Calco2019.Examples.Delay
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[examples]: calco2019-examples.md
[delay]: ../../Silmaril/Semantics/Calco2019/Examples/Delay/Thms.lean
[hangs]: ../../Silmaril/Semantics/Calco2019/Examples/Printing/Hangs/Thms.lean
