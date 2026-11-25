# CALCO 2019 Article 13 in Lean

This page maps the numbered statements of Paul Blain Levy and Sergey Goncharov,
[*Coinductive Resumption Monads: Guarded Iterative and Guarded Elgot*][paper],
to the standalone `Silmaril.Papers.Calco2019` development. The publisher's
[PDF][pdf] has SHA-256
`e9617e110c12a9ab2e99de57c75b2a23ed9191f6721afe92c0bba6a8b7ecb3ab`.

The [definitions][defs] and [theorem view][thms] cover the abstract
development. Definitions use categories with chosen binary coproducts.
Statements involving the initial object ask for one where it is used.
Kleisli coproducts come from the left adjoint of the Kleisli adjunction.

## Numbered statements

| Paper | Status | Lean declarations and scope |
| --- | --- | --- |
| Definition 1 | Checked | `Bimodule` is Mathlib's profunctor with the paper's argument order. [Definitions][free] |
| Definition 2 | Checked | `Bimodule.FreeExtension` and `IsFreeExtension` specify a mediator unique under the two leg equations. [Definitions][free] |
| Definition 3 | Checked | `Bimodule.FreeObject` and `IsFreeObject` use the generator leg. [Definitions][free] |
| Proposition 4 | Checked | `proposition4` gives the free-object equivalence for an initial base. [Theorems][thms] |
| Proposition 5 | Checked | `proposition5` and `proposition5_coprodLeg` characterize free extensions by the coproduct with the free object and recover the coproduct leg. [Theorems][thms] |
| Definition 6 | Checked | `Guardedness` and `MonadGuardedness` give the three guard axioms and the Kleisli guard. [Definitions][defs] |
| Notation 7 | Checked | `Guardedness.nestedMany` handles any positive number of guarded summands, with one- and two-summand specializations. [Nested guards][nested] |
| Proposition 8 | Checked | `proposition8_initial`, `proposition8_comp`, `proposition8_weakening`. [Theorems][thms] |
| Proposition 9 | Checked | `proposition9_greatest` and `proposition9_least` use the total and vacuous guards. [Theorems][thms] |
| Example 10(1) | Checked | The subterminal `Trunc` arrow is guarded in each summand individually and fails the combined guard. [Examples][examples] |
| Example 10(2) | Checked | Powerset has the total guard. The nonempty powerset guard records at least one direct return. [Examples][examples] |
| Example 10(3) | Checked | `pmfGuard` and `pmf_guarded_iff` identify the guard with positive direct-return mass. [Probability][probability] |
| Example 10(4) | Checked | The nonempty-word guard satisfies the axioms for the writer and the left-action extensions. [Writer][writer] |
| Example 10(5) | Checked | The productive nonempty trace guard satisfies all three axioms. [Traces][traces] |
| Definition 11 | Checked | `MonadGuardedness.Preserves` and `GuardedNatTrans` test preservation and guardedness in the entire output. [Definitions][defs] |
| Definition 12 | Checked | `Guardedness.Iterative` requires a unique fixpoint for every guarded body. [Definitions][defs] |
| Lemma 13 | Checked | `lemma13` and `guarded_fixpoint` preserve the other marked output through guarded iteration. [Theorems][thms] |
| Definition 14 | Checked | `Guardedness.Conway` combines guarded fixpoints, naturality, dinaturality and codiagonal. [Definitions][defs] |
| Remark 15 | Checked in the co-Cartesian setting | The guarded and total trace correspondences, their compatibility, and the precise standard-model claims are mapped below. [Remark view][remark] |
| Definition 16 | Checked | `Fixpoints.Uniform` tests the change-of-state square along a functor. The paper's strict coproduct preservation enters Proposition 17. [Definitions][defs] |
| Proposition 17 | Checked | `proposition17` derives dinaturality from uniformity, naturality and codiagonal. Selected coproduct preservation and surjectivity on objects suffice, including the paper's strict identity-on-objects case. [Theorems][thms] |
| Proposition 18 | Checked | `proposition18` derives the Conway laws and uniformity from unique guarded fixpoints. [Theorems][thms] |
| Definition 19 | Checked | `IsGuardedIterative`, `GuardedElgotMonad`, `IsElgot`, and `definition19_divergence`. [Definitions][defs] · [Theorems][thms] |
| Example 20(1) | Checked with source correction | The vacuous guard factors through the left, returning injection. The introductory sentence naming the right injection is reversed. [Theorems][thms] · [Examples][examples] |
| Example 20(2) | Checked | The powerset iteration is the least finite-run solution. The nonempty powerset restriction is a guarded Elgot model. [Examples][examples] |
| Example 20(3) | Refuted as printed | A two-label loop retains the published weights and violates the normalized fixpoint equation. Unit termination mass suffices for the fixpoint, and the positive-return guard admits no natural, uniform PMF-valued selector. [Probability][probability] |
| Example 20(4) | Checked with source corrections | One-letter recursion has no finite-word solution. The singleton extension is Elgot and the stream extension is guarded iterative. The arbitrary inhabited-action claim and the printed universal properties have counterexamples or corrected scopes. [Writer][writer] |
| Example 20(5) | Checked | Productive iteration is the greatest solution and satisfies the guarded Elgot laws. A guarded body has distinct solutions and an unguarded body witnesses the non-total guard. [Traces][traces] |
| Definition 21 | Checked | `ParametrizedGuardedElgotMonad` is a functor into guarded Elgot monads. The parameter maps preserve the Kleisli and iteration operations. [Definitions][defs] |
| Example 22 | Checked | `Exception.parametrizedElgot` checks the parametrized exception family for a guarded Elgot base, including iteration preservation under a change of parameter. [Theorems][thms] |
| Proposition 23(1) | Checked | `proposition23_extension` derives the unique extension from the chosen final coalgebras. [Theorems][thms] |
| Proposition 23(2) | Checked | `proposition23_solution` uses the result-then-state order `Y + X` in the diagram. The nearby prose reverses the summands. [Theorems][thms] |
| Proposition 23(3) | Checked | `proposition23_monad` constructs the monad, with the unit of the fixed-parameter monad followed by rolling. [Theorems][thms] |
| Definition 24 | Checked | `ResumptionGuard` and `resumptionGuardedness_iff` identify the observed guard. `resumptionGuardedness_total` checks preservation of totality. [Theorems][thms] |
| Theorem 25 | Checked | `resumptionElgotMonad` and `theorem25` prove all the laws and the unique characterization by the observation diagram. [Theorems][thms] |
| Corollary 26 | Checked | `corollary26` instantiates Theorem 25 with the family from Example 22. [Theorems][thms] |
| Lemma 27(1) | Checked | `lemma27_suspension_guarded` uses only the guard on the base and proves that the suspension is guarded in the entire output. [Guarded suspension][lemma27] |
| Lemma 27(2) | Checked | `lemma27_base` verifies preservation of the monad structure, guards and iteration by the base embedding. [Theorems][thms] |
| Theorem 28 | Checked | `theorem28` and `Exception.mediatorHom_app` specify the two legs, explicit mediator, guard and iteration preservation, and uniqueness. [Theorems][thms] |
| Corollary 29 | Checked | `corollary29` derives the coproduct with the free guarded Elgot resumption of the identity base. [Theorems][thms] |

## Remark 15 dependencies

- For Goncharov–Schröder Definition 25, `FourInterfaceTrace.run` takes a
  guarded body `(A + U) + B ⟶ C + (D + U)` and `guarded` supplies the
  marked output guard on `A + B ⟶ C + D`. Figure 4(a), (b), (d), (e),
  (f), (g), and (h) are respectively `vanishInitial`, `slideI`,
  `slideII`, `superpose`, `slideIII`, `tighten`, and `yank` in
  `FourInterfaceTrace.LocalLaws`. The remaining field `Lawful.vanishPair`
  is Figure 4(c). Its outer trace takes the actual inner trace and the
  guard supplied by `guarded`. `vanishPair_body` extends the displayed
  two-state presentation to every admissible body with a coproduct of
  two feedback wires. [Figure 4][guarded-traces] · [Trace laws][local] · [Vanishing II][pair]
- For Proposition 32, `lawful_ofConway` derives the trace equations from
  Conway. For the converse, `toFeedback_lawful` restricts them to marked
  initial ports. The reduced laws give the fixpoint equation, naturality
  and dinaturality, then reduced Vanishing II gives codiagonal.
  `FourInterfaceTrace.conwayEquiv` proves both round trips.
  `conway_iterate` gives the recovered dagger by feeding back the
  duplicated body. `toFeedback_eq_of_initial` uses tightening alone
  for independence of the chosen initial object. `totalTraceEquiv`
  compares the direct restriction with the ordinary co-Cartesian
  Joyal–Street–Verity conversion. [Converse][converse] · [Equivalence][profile] · [Compatibility][compatibility]
- `Guardedness.commutativeIdentity` proves the equation from
  `Fixpoints.Uniform J`, using the state reindexing from the chosen
  cofan and the hypothesis that every route preserves its fibers.
  `automatonIdentity` uses the fold. The finite surjective specialization
  used for the usual equational schema is `FiniteCopowers.CommutativeIdentities`.
  [Uniformity instances][automata] · [Finite schema][schema]
- `PointedModel.commutative` proves standard-model validity by strict
  finite reindexing. `SortedTerm.validInPointedDomains_iff` identifies
  the equations valid in the pointed ω-cpo models with those valid in
  total Conway models satisfying the finite schema. The proof goes
  through graph compilation, jump normalization, and the finite
  ranked-system separator. `FiniteMatrix.conway_fails_binaryCycle`
  supplies the categorical incompleteness witness. [Standard model][pointed] · [Completeness][complete] · [Countermodel][independence]

## Introductory results and scope

- [Introduction][intro] covers concrete printing, signature I/O and
  Capretta's delay carrier. [Figure 1][figure] checks the inclusions into
  guarded Elgot monads. The `PolynomialExtension` view treats the
  polynomial illustration in commutative rings. [Polynomial extension][poly]
- `Maybe.hyperextensiveInitial` uses a hyperextensive category with a
  terminal object for `X + 1`. `hyperextensiveMaybeResumption_freeOn`
  separately takes the required final coalgebras.
  `RestrictedResumptions` states the free extensions in the total and
  guarded iterative categories. [Maybe][maybe] · [Restricted universality][restricted]
- Remark 15 covers the co-Cartesian specialization of guarded trace
  theory and states completeness as semantic equational consequence.
  General symmetric monoidal guarded trace theory, a separate syntactic
  deduction calculus, Capretta's intensional-type-theory interpretation,
  and the quotient and process-equivalence research directions of §6
  are outside this development.

## Checking

```sh
lake build --wfail \
  +Silmaril.Papers.Calco2019.Thms \
  +Silmaril.Papers.Calco2019.Lemma27 \
  +Silmaril.Papers.Calco2019.Remark15 \
  +Silmaril.Papers.Calco2019.RestrictedResumptions
```

[paper]: https://doi.org/10.4230/LIPIcs.CALCO.2019.13
[pdf]: https://drops.dagstuhl.de/storage/00lipics/lipics-vol139-calco2019/LIPIcs.CALCO.2019.13/LIPIcs.CALCO.2019.13.pdf
[guarded-traces]: https://doi.org/10.1007/978-3-319-89366-2_17
[defs]: ../../Silmaril/Papers/Calco2019/Defs.lean
[thms]: ../../Silmaril/Papers/Calco2019/Thms.lean
[free]: ../../Silmaril/Semantics/Calco2019/FreeExtensions.lean
[nested]: ../../Silmaril/Semantics/Calco2019/Nested.lean
[examples]: calco2019-examples.md
[probability]: calco2019-examples-probability.md
[writer]: calco2019-examples-writer.md
[traces]: calco2019-examples-traces.md
[intro]: calco2019-introduction.md
[remark]: ../../Silmaril/Papers/Calco2019/Remark15.lean
[lemma27]: ../../Silmaril/Papers/Calco2019/Lemma27.lean
[local]: ../../Silmaril/Semantics/Calco2019/Trace/ProfileLaws/Defs.lean
[pair]: ../../Silmaril/Semantics/Calco2019/Trace/ProfileEquivalence/Defs.lean
[converse]: ../../Silmaril/Semantics/Calco2019/Trace/Converse/Thms.lean
[profile]: ../../Silmaril/Semantics/Calco2019/Trace/ProfileEquivalence/Thms.lean
[compatibility]: ../../Silmaril/Semantics/Calco2019/Trace/Compatibility/Thms.lean
[automata]: ../../Silmaril/Semantics/Calco2019/Trace/Automata/Thms.lean
[schema]: ../../Silmaril/Semantics/Calco2019/Trace/IterationTheory/Commutative/Defs.lean
[pointed]: ../../Silmaril/Semantics/Calco2019/Trace/IterationTheory/PointedModel/Thms.lean
[complete]: ../../Silmaril/Semantics/Calco2019/Trace/IterationTheory/SortedTerms/Thms.lean
[independence]: ../../Silmaril/Semantics/Calco2019/Trace/CounterSemiring/Independence/Thms.lean
[poly]: ../../Silmaril/Papers/Calco2019/Examples/PolynomialExtension.lean
[figure]: ../../Silmaril/Papers/Calco2019/Figure1.lean
[maybe]: ../../Silmaril/Semantics/Calco2019/Maybe/Hyperextensive/Iteration/Thms.lean
[restricted]: ../../Silmaril/Papers/Calco2019/RestrictedResumptions.lean
