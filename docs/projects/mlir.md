# MLIR-style scalar SSA

The checked fragment in [`Silmaril.SSA.MLIR.Arith`](../../Silmaril/SSA/MLIR/Arith)
models scalar signless `arith.constant`, `arith.addi`, and `arith.muli` on positive
bit widths. Addition and multiplication have the empty overflow flag set and
compute modulo (2^w). There are no flags, effects, poison values, parsers,
or CFGs in this fragment.

A context `Γ = [w₀, …, wₙ₋₁]` denotes the product of the corresponding
`BitVec` types. A block denotes a total function from this product to its
result type. Each instruction reads typed references and extends the context
with one result. A yield projects a reference. The region-bearing form adds
a pure scoped application with one explicit argument, one single-block body,
and one yielded result. The body starts with a singleton context, so an outer
value enters only as the explicit argument. Applications can nest.
[`Defs.lean`](../../Silmaril/SSA/MLIR/Arith/Defs.lean)

## Checked translations

| Theorem | Statement |
| --- | --- |
| `Block.toLambdaSSA_hasType` | The lowered LambdaSSA region has one exit with the declared result type. |
| `Block.toLambdaSSA_eval_iff` | On every typed input its finite outcomes consist exactly of exit zero carrying the source denotation. |
| `Block.toLetIter_hasType` | The encoded LetIter term has the corresponding context and result type. |
| `Block.toLetIter_eval_iff` | On the corresponding positional environment its finite results are exactly the source denotation. |
| `Examples.double_lowering` | Rewriting `addi x x` to a block that materializes two and multiplies by it preserves the result at every width. |
| `Examples.doubleMul_lambdaSSA`, `Examples.squareAdd_letIter` | The translated examples return (400 mod 256 = 144) and ((20^2 + 20) mod 256 = 164), respectively. |

The lowering uses LambdaSSA’s existing `Tm.let₁`, primitive applications
and a single `Region.br` exit. A scoped application becomes a lexical let for
its argument inside the let that binds its result. The proof checks its body
with an arbitrary ambient suffix to the typing context and runtime environment.
The existing `Isotope.Morphism.SSAIter.encodeSingle` applies because the lowered
region is scoped and has one exit. The bridge reuses `encodeSingle_hasType`
and `encodeSingle_eval_iff`. The ambient calculi already have an isomorphism
`Isotope.Institution.Observational.iterSSAIso` on the single-exit observational
quotients. [LambdaSSA theorems](../../Silmaril/SSA/MLIR/Arith/Thms.lean) ·
[LetIter theorems](../../Silmaril/SSA/MLIR/Arith/LetIter/Thms.lean) ·
[Examples](../../Silmaril/SSA/MLIR/Arith/Examples/Thms.lean) ·
[Existing calculus results](ssa.md)

```sh
lake build --wfail Silmaril.SSA.MLIR.Arith.Examples.Thms
```

## Roadmap

1. **Plain and region signatures.** A plain signature has a set of sorts and
   operation symbols with ordered operand and result sort lists. Begin with
   total models that assign a carrier (A_s) to each sort and a function between
   the corresponding products to each operation. Extend a region signature
   with an ordered list of region profiles per operation, each specifying
   parameter sorts, yielded sorts, and which captures are admitted. For
   isolated regions, an operation receives one extra argument per region
   of type (prod A_{mathrm{params}} 	o prod A_{mathrm{yields}}). Add
   captures later as explicit environment arguments, and require translation
   to respect that typing and binding structure.
2. **Signature change and institutions.** Start with typed symbol maps
   (sigma : Sigma 	o Sigma') that map sorts and operation symbols and
   preserve all mapped profiles, including region scopes. Sentences are
   equations between blocks with the same typed input and output interfaces,
   universally quantified over their inputs. (mathrm{Sen}(sigma)) maps
   symbols throughout a block, including its nested bodies. The reduct
   (M'|_sigma) pulls carriers and operation interpretations back along the
   symbol map. With discrete model categories initially, prove functoriality
   of renaming and reduct and prove the satisfaction condition
   (M' models mathrm{Sen}(sigma)(e) iff M'|_sigma models e) by a
   denotation lemma. Its region case uses the induction hypothesis at each
   parameter assignment, then the mapped operation's interpretation. These
   institution laws for dialect signatures are planned. Use the repository's
   [institution interface](../../Silmaril/Logic/Institution/Basic.lean).
3. **Categorical semantics.** Use contexts as objects and tuples of block
   results as arrows modulo a typed congruence closed under substitution
   and region contexts. Use projections for identity and capture-avoiding
   substitution or sequencing for composition. Prove the category and finite-product laws and interpret it
   in a category of total functions, with products for contexts. For
   region-bearing models, require an interpretation of the binders, for
   example using exponentials in a cartesian closed target for the pure
   function-valued region arguments above. Compare the resulting category
   and the LambdaSSA/LetIter interpretations on their common fragment using
   the checked lowering and prove naturality under signature change before
   asking for an equivalence. Effectful or iterative regions will require
   explicit laws of the chosen model, with the existing distributive Freyd
   and Elgot developments as candidates. [SSA categorical results](ssa.md)
4. **Compilation.** A lowering may implement an operation by a typed target
   block with formal operands and, for region-bearing operations, translated
   scoped bodies. Composition then substitutes blocks for operations.
   `Examples.double_lowering` checks one such replacement in the total
   bitvector model. Prove its contextual lifting before using it as a
   general pass. Equality suits this pure deterministic slice. For a
   restricted or nondeterministic source, specify an admission predicate,
   input and observation correspondence, and show that the related target
   behaviors are included in the source's allowed behaviors on admitted
   inputs. A compiler validation result is semantic preservation or
   refinement under those explicit hypotheses.

## Staged dialect coverage

| Stage | Intended slice |
| --- | --- |
| Tiny scalar dialects | Add a few flag-free bit operations and comparisons, then tuples and explicit block arguments as needed. Build the signature-change and scoped-substitution laws over these examples. |
| Static tensor | A tensor of shape `[d₀, …, dₖ₋₁]` is a total function from `Fin d₀ × … × Fin dₖ₋₁` to its element carrier, with a singleton index domain for rank zero. Start with constants, elementwise maps and shape-checked indexing. Use extensional equality. |
| Scoped affine | Integer affine maps and bounded single-block loops with typed loop-carried parameters and yields. Begin without mutable memory and relate admitted loops to finite folds. |
| Minimal LLVM and future x86 validation | Start with pure single-block scalar integers, concrete defined inputs, constants, unflagged modular add/subtract/multiply and a return. Reject every instruction outside the profile. Initially exclude flags, shifts/division, `freeze`, `undef`, poison inputs and instructions that can produce poison, pointers, memory, calls and control flow. Keep unsupported syntax an admission error, immediate UB a separate execution outcome or semantic condition, poison a deferred value state and `undef` a use-dependent choice in extensions. Add one feature at a time and prove semantic refinement on the admitted defined inputs against a specified x86 observation and ABI. |
| Larger dialects | Add small pure static-shape **StableHLO** operators first. For **Triton/Gluon**, start with layout-indexed pure tensor operations, then specify memory and parallel execution explicitly. For a **C dialect**, start with pure scalar expressions whose C types and definedness preconditions are explicit and relate those to the C semantics. |

## Sources

- The [MLIR Language Reference](https://mlir.llvm.org/docs/LangRef/) specifies
  blocks and regions. The [Arith dialect reference](https://mlir.llvm.org/docs/Dialects/ArithOps/)
  specifies the scalar operations and overflow flags.
- [VeIR](https://github.com/opencompl/veir/tree/4888294eb0bd4acba85ba530f57408b356160f05)
  is a design reference for MLIR in Lean. Its
  [license](https://github.com/opencompl/veir/blob/4888294eb0bd4acba85ba530f57408b356160f05/LICENSE)
  is Apache-2.0 with LLVM exceptions. This development uses original code and
  the existing Silmaril LambdaSSA and LetIter APIs.
- The [LLVM Language Reference](https://llvm.org/docs/LangRef.html) and
  [LLVM IR Undefined Behavior Manual](https://llvm.org/docs/UndefinedBehavior.html)
  specify the future LLVM validation boundary.
