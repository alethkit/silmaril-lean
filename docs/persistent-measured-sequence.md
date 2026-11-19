# A persistent measured sequence

`MeasuredSequence` models persistent edits with a cached element count at each
join. It is inspired by the use of element measures in Unison's sequence
structures, not a model of the Unison runtime or its finger-tree digits.
This complements paged ropes: the unit here is a generic element, and the
focus is the behavior of path-local edits before an explicit rebuild.

`append`, indexed lookup and replacement, `splitAt`, and `splice` implement
ordinary list behavior. Splitting at a join boundary returns both original
children; replacement rebuilds only the path it takes. Splits clip at the end,
replacement outside the sequence has no effect, and splicing past the end
appends the inserted sequence. The operations preserve the validity invariant
(exact cached sizes and no empty children at a join), when their inputs are
valid. No claim about runtime allocation or automatic rebalancing is made.

`normalize` rebuilds from elements by a deterministic midpoint bisection. It
preserves the list and returns a valid tree whose left child at each join has
the floor half of the elements. It is idempotent, and two trees normalize to the
same tree exactly when their lists agree. `normalEquiv` relates only the
normalized subtype to lists, not the raw editable shapes. This is an in-memory
generic representation: it does not choose a wire codec or names for elements.

```sh
lake build --wfail Silmaril.Semantics.MeasuredSequence.Thms
lake env lean -DwarningAsError=true --run tests/semantics/MeasuredSequence.lean
```
