# Typed interpretations of pure MLIR dialects

An operation interpretation maps sorts and assigns each source symbol an image
at its mapped profile. An image can forward an operation with the same slot
interface or expand a regionless primitive into a block of target terms. In an
expansion, the mapped operands form the input context and each mapped result
gets one term. Substitution instantiates the block. An operation with isolated
regions is forwarded, and every yield term is translated in its own mapped
parameter context. Region-bearing operation templates that invoke or transform
their source regions are outside this interface. [Translation definitions](../../Silmaril/SSA/MLIR/Institution/Translation/Defs.lean)

## Composition and semantics

Under `Silmaril.MLIR.Institution.Interpretation`, `term_id`, `term_subst`
and `term_comp` give the syntax laws, and `id_comp`, `comp_id`, and
`assoc` give the laws on interpretations themselves. `syntaxFunctor` acts
on the raw substitution category, with laws `syntax_id` and `syntax_comp`.
`denote_term` equates evaluation of a lowered term in a target model with
evaluation of the original term in the induced source model. `syntax_denote`
gives the functor equality, `reduct_comp` gives the composition law for induced
models, and `satisfaction` gives the corresponding equivalence for equations.
[Translation theorems](../../Silmaril/SSA/MLIR/Institution/Translation/Thms.lean)

The worked dialect adds a unary `double` primitive to the scalar arithmetic
signature. The independent source model uses addition. The lowering expands
`double` into multiplication by a materialized two at the result width.
`Translation.Examples.lower_reduct` identifies the induced and independently
specified source models at every positive width. `lower_satisfaction` applies
this to all source equations. `scopedDouble_denote` checks a doubling inside an
isolated body, with a separate unused outer input. `scopedDouble_i8` computes
144 from 200 at width eight. [Lowering example](../../Silmaril/SSA/MLIR/Institution/Translation/Examples/Thms.lean)

## Observational quotient and products

Within `Silmaril.MLIR.Institution.Syntax.Observational`, two blocks represent
the same arrow exactly when all result slots agree at all typed inputs for
each selected model (`ofBlock_eq_iff`). To interpret equations, select the
models that satisfy them. The empty context is terminal (`emptyIsTerminal`).
Context concatenation and its slot projections form a binary product
(`binaryFanIsLimit`), giving `HasFiniteProducts`. Every selected model
interprets the quotient in `Type` (`quotient_denote`). An interpretation
acts on quotient arrows when each selected target model induces a selected
source model (`quotient_translate`).
[Quotient theorems](../../Silmaril/SSA/MLIR/Institution/Syntax/Observational/Thms.lean) ·
[Product theorems](../../Silmaril/SSA/MLIR/Institution/Syntax/Observational/Products/Thms.lean)

## Common slice with LambdaSSA and LetIter

The comparison uses the image of the repository's scalar arithmetic
`Block Γ w` for each ordered list of positive input widths `Γ` and single
positive result width `w`. This includes constants, modular addition and
multiplication, and unary isolated application. The MLIR quotient uses the
concrete bitvector model. On the other side, observations use the existing
`Block.toLambdaSSA` and `Block.toLetIter` encodings, the concrete arithmetic
instruction relation, the unit state, and every environment of type `Env Γ`.
The LambdaSSA observation includes the exit label and returned value. The
LetIter observation includes the returned value with the empty free environment.
`Arith.arrow_eq_iff_lambdaSSA_eval` and `Arith.arrow_eq_iff_letIter_eval`
give both directions for these return observations.
[Comparison theorems](../../Silmaril/SSA/MLIR/Institution/Syntax/Observational/Arith/Thms.lean)

The existing universal `Region.Obs` and `Tm.Obs` quantify over instruction
relations, environments, faults and divergence. Restricting their evaluation
component gives `Arith.arrow_eq_of_lambdaSSA_obs` and
`Arith.arrow_eq_of_letIter_obs`. The converse fails on this slice.
`Arith.double_eq` identifies addition-based and multiplication-based doubling
in the bitvector quotient. `Arith.double_not_lambdaSSA_obs` uses an instruction
relation that runs addition and has no constant step to distinguish the two
lowerings. `Arith.double_not_letIter_obs` transfers the distinction via the
existing single-exit observation theorem. These results compare equality of
parallel arrows on the specified slice. A compositional comparison functor
into a target category with restricted observations remains to be constructed.
[Existing observational interfaces](ssa.md) ·
[Comparison theorems](../../Silmaril/SSA/MLIR/Institution/Syntax/Observational/Arith/Thms.lean)

The definitions build directly on the typed syntax, raw category and arithmetic
translation in [#2150](https://github.com/hiloopai/silmaril-lean/pull/2150) at
`8fdd2cad831858af0f76c994eac4c0877734aac4`, and the scalar semantics,
doubling example and single-exit encodings in
[#2133](https://github.com/hiloopai/silmaril-lean/pull/2133) at
`01b6b841efed69df42d39176333a54332e4da049`. The universal observation comparison
uses `SSAIter.encodeSingle_obs_iff` from
[#74](https://github.com/hiloopai/silmaril-lean/pull/74) at
[`65aa4f9ffa2374e15ab63a714a52840dee236afe`](https://github.com/hiloopai/silmaril-lean/commit/65aa4f9ffa2374e15ab63a714a52840dee236afe).

## Check locally

```sh
targets='+Silmaril.SSA.MLIR.Institution.Translation.Examples.Thms +Silmaril.SSA.MLIR.Institution.Syntax.Observational.Products.Thms +Silmaril.SSA.MLIR.Institution.Syntax.Observational.Arith.Thms'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
```
