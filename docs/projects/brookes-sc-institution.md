# SC signatures and institution

A target supplies the semantics of a fixed world. Over that world,
signatures choose which operations to expose and which labels to give
them.
[Institution header](../../Silmaril/Logic/BrookesSC/Thms.lean)
[Effect interface](../../Silmaril/Games/BrookesSC/Thms.lean)

## Fixed worlds and signature arrows

A `World` fixes thread IDs, typed store cells, mutex IDs, and the reply sorts
available for external operations. A primitive load returns the type of its
cell. A primitive store carries a value of that type. Acquire and release
are separate commands with unit replies. Every primitive carries its
thread, and memory primitives also carry their access mode. A world can
give different cells different types, generalizing the natural-number
cells used by the [Track A SC machine]. External operations take their
reply type from the named sort. A label has one designation, and
multiple labels may share a designation.

A signature arrow is a function on labels in every designation fiber.
Thus an interface extension can include the old labels, and a renaming
can permute labels within each fiber. Identifying aliases is allowed within
a fiber. Primitive aliases have a single meaning in every model. Distinct
external labels of the same sort may have different meanings, so a reduct
along a map that identifies them interprets both by the same target
operation. Categorical identities and composition are the identity and
composition of these fiber maps. A world change would need a separate
state and primitive transport theorem (for example, conjugation by
bijections preserving the typed cells and mutex ownership).

`events` packages designations and labels as dependent requests in the
existing `Silmaril.Games.Sig`. `eventHom` sends requests forward and passes
replies back unchanged. Its identity and composition laws hold for
`Games.Sig.Hom`. `eventFunctor` bundles the maps in the opposite of the
existing game category, where the underlying forwarding strategy implements
source requests on top of the target. The [Track A interaction signature]
uses the same request/reply variance. Its backward reply map can change
the value a continuation receives, and its forward request map can
redirect a read to another cell of the same type. `aliasReads_not_liftable` checks
this failure for an effect map collapsing reads of two Boolean cells.

Weakening here is forward translation into a larger signature, with
restriction of its model in the other direction. Hiding an operation in
a running program needs a typed handler or an observation policy. The
[Track A sequential operators] give the typed handler construction.
[SC interface projection] filters completed events while retaining source
execution witnesses. Its synchronization and race results require explicit
coverage hypotheses. In particular, deleting a mutex handoff or an
intervening write can change the inferred ordering. Neither operation
follows from the fixed-world signature laws.

## Sentences, models, and satisfaction

`Program` is a well-founded tree of typed calls and returns. Continuations
can branch on replies, including over infinite reply types. A sentence
`lhs ≤ rhs` consists of two programs of the same result type for each
input valuation. Two opposing inequations express observational equality
when the target order is antisymmetric, and mutual refinement in general.

A `Target` supplies a family of ordered carriers indexed by return type,
return, monotone sequencing, and the meaning of each primitive. A
`Model` interprets the external labels in that family. Model morphisms are
pointwise refinement of those interpretations, with identity and
composition from the target preorder. `Model.eval_mono` extends these
arrows to observations of whole programs by induction. A model reduct
precomposes the external interpretation with the signature map. The reduct
functor also restricts proofs of pointwise refinement.

For a map from S to T, `Model.eval_translate` identifies evaluation of the
translated tree in a T-model with evaluation of the original tree in its
reduct. The call case uses the identical primitive in both signatures, or
the precomposed external interpretation, and the inductive equality for
every reply continuation. Satisfaction follows by applying that equality
on both sides for every input. The repository's `Room` functor packages
this proof, and `Institution.sentenceFunctor` and `Institution.modelFunctor`
give the covariant sentence and contravariant model functors. The generic
institution laws use this syntactic induction and never assume the
satisfaction condition as a law of the target.

The proof examples instantiate the target with may outcomes of an
explicitly ordered run over a heterogeneous store and a shared mutex.
They only observe successfully returned values and final states. An open
write/read-back inequation is checked through a nonidentity inclusion
and its reduct. Swapping which external operation is selected changes
the truth of the translated inequation. The same target checks owner-only
release and acquisition by another thread after release. It also exhibits
two models with a refinement arrow in one direction only.
[State examples](../../Silmaril/Proofs/Logic/BrookesSC/Examples.lean)
[Aliasing example](../../Silmaril/Proofs/Games/BrookesSC/Examples.lean)

## Brookes and tree comparisons

To instantiate `Target` on the Brookes closed traces, supply the carrier
of closed traces at each result type, their refinement preorder, return
and sequencing, and prove that sequencing is monotone in its first
argument and pointwise in its continuation. Interpret each `Primitive`
using the corresponding closed one-step computation with its typed reply
and ownership guard. Those SC obligations belong to the specialization.
Compare choice, parallel scheduling, and the effects of environment steps
using the Brookes core semantics. The current syntax explicitly orders
primitive calls and has no scheduler or parallel constructor.

For an ITree or CTree comparison, use the dependent event interface to
encode the call nodes and prove that interpretation commutes with return
and call, including reply-dependent continuations. The
[Track A interaction institutions] supply observation-bound sentences,
a category of bijective-reply relabelings, and a guarded Elgot fold. The SC institution supplies structured program inequations with
forward syntax translation and reduct by precomposition. An SC arrow
has identity reply maps and hence meets the Track A reply-bijectivity
requirement. A direct adapter can use that category when it is available.
Specify the observations before relating the richer trees, in particular
how to treat internal steps, choice, refusal and divergence. The regression target records successful
outcomes only. Primitive SC and its access designations make no judgement
about races, undefined behavior, fairness or starvation.

## Check commands

```sh
targets='+Silmaril.Logic.BrookesSC.Thms +Silmaril.Games.BrookesSC.Thms +Silmaril.Proofs.Logic.BrookesSC.Examples +Silmaril.Proofs.Games.BrookesSC.Examples'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
for file in Silmaril/{Logic,Games,Proofs/Logic,Proofs/Games}/BrookesSC/*.lean; do
  module=${file%.lean}
  LEAN_NUM_THREADS=1 SILMARIL_REPLAY_MODULE=${module//\//.} \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean || exit
done
```

## References

- J. A. Goguen and R. M. Burstall, *Institutions: Abstract Model Theory for
  Specification and Programming*, 1992, §2.1 and §2.5. [DOI](https://doi.org/10.1145/147508.147524)
- J. Goguen and G. Roşu, *Institution Morphisms*, 2002, §3.
  [DOI](https://doi.org/10.1007/s001650200013)
- L. Lamport, *How to Make a Multiprocessor Computer That Correctly Executes
  Multiprocess Programs*, 1979. [DOI](https://doi.org/10.1109/TC.1979.1675439)
- S. Brookes, *A semantics for concurrent separation logic*, 2007.
  [DOI](https://doi.org/10.1016/j.tcs.2006.12.034)
- L.-Y. Xia et al., *Interaction Trees: Representing Recursive and Impure
  Programs in Coq*, 2020. [DOI](https://doi.org/10.1145/3371119)
- N. Chappe et al., *Choice Trees: Representing Nondeterministic, Recursive,
  and Impure Programs in Coq*, 2023. [DOI](https://doi.org/10.1145/3571254)

[Track A interaction signature]: https://github.com/hiloopai/silmaril-lean/pull/3543
[Track A sequential operators]: https://github.com/hiloopai/silmaril-lean/pull/3564
[SC interface projection]: https://github.com/hiloopai/silmaril-lean/pull/3559
[Track A SC machine]: https://github.com/hiloopai/silmaril-lean/pull/3539
[Track A interaction institutions]: https://github.com/hiloopai/silmaril-lean/pull/3576
