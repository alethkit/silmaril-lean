# Single-exit λSSA region correspondence with RVSDG

This increment lifts the [typed expression correspondences](rvsdg-lambdassa.md)
to actual λSSA regions. An admitted region has region-level `let₁` and
`case` binders and exits only through `br 0`. The branch argument is
ordinary λSSA expression syntax. `exitExpression` converts these region
constructors to their expression counterparts and returns the branch
argument at exit zero. It preserves de Bruijn indices, including the
payload binders of a case. Its computation is equivalent to the
syntax-directed `ExitExpression` relation.
[Definitions](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Region/Defs.lean)

The RVSDG admission still comes from the typed expression fragments.
The recovered expression must be unary straight-line code or a terminal
multiway switch whose arms each return one captured payload port.
`lowerRegion` and `lowerGammaRegion` inhabit the graph fibres from these
forms. `raiseRegion` and `raiseGammaRegion` inhabit the reverse fibres
using canonical region-level binders and explicit jumps to label zero.
Every witness gives the repository's exact `Region.HasType` judgement
with a singleton label signature.

`ExitExpression.denotes` maps any structural expression denotation to a
structural region denotation by composing with the label-zero injection.
The proof commutes that injection through the repository's categorical
binder and contextual case. Both graph soundness theorems identify this
arrow with the RVSDG graph arrow under the typed input map and singleton
exit observation in a strong Elgot Freyd model. The admitted regions use
no iteration. [Theorems](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Region/Thms.lean)

The fixture lowers an actual region-level primitive let and recovers a
nested three-way region-level case spine. It also checks rejection of
a nonzero exit and of a CFG binder. Computed selectors, branch-local
instructions, mixed straight-line and γ composition, and multiple exits
remain extensions. A sentence-level comorphism additionally needs
reindexing naturality and a model comparison that preserves and reflects
the shared observation. [Fixture](../../../../tests/ssa/RVSDGSingleExit.lean)

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Region.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Region.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Region.Thms
```

The [categorical project sources](../semantics/rvsdg-categorical.md#sources) pin the
studied PDFs. This increment uses arXiv:2411.09347v1, §§3 and 5.3, for
λSSA syntax and interpretation, and arXiv:1912.05036v2,
§§4.1.1–4.1.2 and 5.2.2 for the RVSDG fragment and structured recovery.
