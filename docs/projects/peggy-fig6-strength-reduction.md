# Figure 6(c–d) strength reduction

This development checks the second rewrite in §3.1, Figure 6(c→d),
printed p. 15 of arXiv:1012.1802v3. The figure keeps the sample count
`P`, changes the sampled stream from `5 * θ₁(0, 1 + x)` to a θ with
initial value zero, and feeds that θ back through addition of five.
The paper refers to the earlier derivation in §1.2, especially scaling
through θ and distributivity over addition in (1.2) and (1.1), printed
p. 8. The general push-through-θ schema is in Appendix A.1, printed
p. 74. [Figure 6](https://arxiv.org/pdf/1012.1802v3#page=15) ·
[(1.1)–(1.2)](https://arxiv.org/pdf/1012.1802v3#page=8) ·
[Appendix A.1](https://arxiv.org/pdf/1012.1802v3#page=74)

## Matched fragment and law

The [matcher](../../Silmaril/SSA/Peggy/Worked/StrengthReduction/Defs.lean)
checks a typed count multiplication with a designated nullary factor
on the left and an actual θ on the right. The θ initializer must be
the designated nullary base. Its feedback node must be the designated
unary step with the θ itself as the operand. The worked model
interprets the unary step as `1 + x`, the factor as five, the base
as zero, and the new binary feedback as `5 + scaled`.

The interpretation contract separately certifies the defined base and
factor, the folded scaled initializer, and the equality of partial
feedback computations. The last premise says that stepping and then
scaling agrees with scaling and then applying the new addition. It
compares optional values, so a mismatch in definedness also violates
the premise. The matched nullary rows guarantee invariance at all
indices. Counts and pure operations suffice for this fragment.

`scaled_recurrence` derives the new θ equation from the original node
equations. At iteration zero, it uses the folded initializer
(`5 * 0 = 0` in the worked model). At a successor, it uses only the
preceding index and `5 * (x + 1) = 5 + 5 * x`. The proof handles both
defined and bottom predecessor samples by strict lifting.

## Checked cyclic rewrite

The executable rewrite adds a binary add row that reads the scale
address, then replaces that address's opcode and operands with the
new θ pointing back to the add row. The resulting graph has an actual
two-row feedback cycle. The initial append is acyclic relative to
the old table. The subsequent replacement, which creates the cycle,
uses its own contextual rewrite proof.

`Match.lifted_solution` proves that the appended source's streams
solve the candidate's simultaneous equations. The changed row uses
the derived recurrence and every other row keeps its equation. The
independent demand-rank check admits the actual target, and
well-founded uniqueness gives the exact ordered Figure 11 result.
The graph keeps its old counter, pass expression, eval count, and
other output dependencies. It also retains the old row table.

## Worked composition and limits

The regression starts with the cyclic Figure 6(b) fixture from
[#4171](https://github.com/hiloopai/silmaril-lean/pull/4171). It runs
the existing E-PEG code-motion match, replay and selection for (b→c),
then matches and rewrites the generated multiplication at address 8.
The resulting θ reads `[1, 10]`, and the new add reads `[6, 8]`.
The same eval samples the new θ at the original pass count.
Lean checks the final graph's rank and proves its ordered results are
`[15, 3, 3, 15]` at every index. The reachability regression confirms
that the retained original multiplication row is outside the
dependency closure of the selected roots.

A total arithmetic interpretation with an incorrect new addition
still meets the (b→c) law. It fails the strength-reduction law on
predecessor zero, where the two feedback computations return five
and six. Definedness of the operands alone would allow that mismatch.

This covers the pure typed PEG stages from (b) through (d). It
produces and checks the rewritten graph. Global cost selection,
a runtime speedup, conversion to the source program in (e), and
Java, memory, or alias behavior remain outside scope.

```sh
lake build --wfail +Silmaril.SSA.Peggy.Worked.StrengthReduction.Thms PEGCoreTests PEGRulesTests PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.Worked.StrengthReduction.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
