# Countably nondeterministic CALCO resumptions

[CALCO 2019, article 13, §1.2, p. 13:4][paper] takes the countable
nonempty powerset as the base monad and uses the signature functor
`Z ↦ Σ a, B a → Z`. An immediate alternative either returns a value or
prints an `a` and waits for a reply in `B a`.

[CountableResumption][layers] defines `Choice`, `Step`, and `Layer`.
The lawful monad on `Choice` uses singleton return and countable unions
of nonempty sets for Kleisli composition. Enumeration by the natural
numbers presents each layer as a quotient of a polynomial. This permits
arbitrary reply types. Countability restricts the set of immediate
alternatives at a node.

[Coalgebras][instances] defines the signature and instantiates the paper's
`InitialResumptions` and `FinalResumptions` for the actual parameter family.
The two monads are available through `inductiveResumptions.monad` and
`coinductiveResumptions.monad`. Their carriers use Mathlib's
`QPF.Fix` and `QPF.Cofix`. `bisim_iff` characterizes equality of
coinductive resumptions through the lifted bisimulation relation.

`inductive_wellFounded` and `inductive_no_infinite_branch` check
branchwise termination. With arbitrary reply types there can also be
an action whose reply type is empty, so the branchwise result means
the absence of an infinite chain of answered actions.
`forever_infinite_branch` gives an infinite productive branch for
any action with a reply. `printingEquiv` and `printingEquiv_natural`
identify the singleton-reply signature with the printing functor
`A × -`.

```sh
lake build --wfail +Silmaril.Papers.Calco2019.Examples.CountableResumption
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[layers]: ../../Silmaril/Semantics/Calco2019/Examples/CountableResumption/Thms.lean
[instances]: ../../Silmaril/Semantics/Calco2019/Examples/CountableResumption/Coalgebras/Thms.lean
