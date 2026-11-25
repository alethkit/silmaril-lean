# The singleton writer extension in CALCO 2019

Example 20(4) of [Levy and Goncharov, CALCO 2019, article 13][paper], p. 13:10,
extends the ordinary writer `A* × X` by a left action on a singleton. In
[SingletonWriter][writer], `Model` is Mathlib's writer transformer over
partiality with the free monoid on the alphabet. The classical equivalence
`observe` identifies its carrier with `(List A × X) ⊕ PUnit`.

`observe_pure` checks the empty output word on pure return. `observe_bind`
checks concatenation on success and the singleton result if either observation
diverges. `elgot_isElgot` reuses the lawful Elgot writer transformer and the
CALCO type bridge. The instance supports arbitrary loop bodies, including the
ones guarded by a nonempty word. The extension by infinite streams and
arbitrary left actions are outside this slice.

```sh
lake build --wfail +Silmaril.Papers.Calco2019.Examples.SingletonWriter
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[writer]: ../../Silmaril/Semantics/Calco2019/Examples/SingletonWriter/Thms.lean
