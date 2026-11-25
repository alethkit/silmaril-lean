# Python structural operational semantics

This is an implementation proposal for a bounded scope of Python semantics.
Start with a labelled, relational core and prove its correspondence with a small
rule presentation. Reuse the existing operational institution for step claims
and the operational policy API for entry, outcomes and safety. Compare Python
and WebAssembly at those interfaces. A compiler between them is outside the
first slice.

## Interfaces in use

| Public interface | What the proposal can use |
| --- | --- |
| [Operational transitions](../../Silmaril/Logic/Operational/Defs.lean) and [run transport](../../Silmaril/Logic/Operational/Thms.lean) | `Signature` fixes state and label types. `Signature.Hom` maps both forwards. `System F` adds an edge predicate over a shape and `System.Hom` requires one target step per source step with the mapped label. `System.Hom.runs` transports CSLib `MTr` with the mapped labels in order. `System.forget` discards the edge predicate. |
| [Operational policy](../../Silmaril/Semantics/Operational/Policy/Defs.lean) and [program interface](../../Silmaril/Semantics/Operational/Program/Defs.lean) | `OpSem` has an unlabelled step and finite observation relation. `WithUB` adds a state predicate, and `HasOpSem` adds relational initialization. `OpSim` maps a source step to a possibly empty target path, compares the same observation type, and preserves possible observations and UB. `OpSim.safe_of_safe` transfers target safety back to the source. |
| [Machine shapes](../../Silmaril/Logic/Operational/Machines/Thms.lean) and [Core adapter](../../Silmaril/Wasm/Institution/Operational/Thms.lean) | `WasmShape.signatures = toStack ⋙ StackShape.signatures`. `Institution.Operational.system P host` supplies actual `Core.Step P host` with label `Unit`. `encode` and `decode` are inverse, and `step_iff` proves exact one-step satisfaction. |
| [Wasm execution and UB](operational-ub.md), [program entry](opsem-programs.md) and [SpecTec bridge](wasm-spec-bridge.md) | The intrinsic integer/local and one-memory slices have guarded finite-outcome results. The versioned SpecTec whole-step results have profile, host and configuration hypotheses. The Core operational adapter alone supplies no result, instantiation or component equivalence. |

The Core typing-policy example is [`Intrinsic.rawSem`](../../Silmaril/Wasm/Execution/Core/Intrinsic/OpSem/Defs.lean).
It enforces `ConfigOk` on host-free small steps and observations.
[`State.raw_safe` and `State.may_iff`](../../Silmaril/Wasm/Execution/Core/Intrinsic/OpSem/Thms.lean)
apply at the erasure of an intrinsic state. `observeResult` keeps a Core trap
distinct from returned values and uncaught exceptions. Division by zero and
out-of-bounds memory access in the relevant Wasm profiles are specified traps.
The one-memory fixture also gives a well-typed `memory.size` outside that
slice's admission policy. A declared divergent host call has a Core self-loop.
A missing host outcome and a component request pending an embedder reply
require their own interpretation. [Core steps](../../Silmaril/Wasm/Execution/Core/Step.lean),
[intrinsic policy test](../../tests/wasm/intrinsic-machine/OpSem.lean),
[memory test](../../tests/wasm/memory-profile/Regression.lean),
[entry test](../../tests/wasm/module-entry/Regression.lean)

## Rule presentations and their category

Use a shape `Σ = (State, Label, Judgment, edge)`, with a naming map
`edge : State × Label × State → Judgment`. Use an injective tag in concrete
presentations to keep edge names distinct. The judgment carrier can also
name auxiliary judgments for contexts and intermediate layers. A ground rule
is a finite list of premises and a conclusion in `Judgment`. A presentation
`R` is a set of ground rules, including the instances of any schema whose
side conditions hold. Define `Derives R j` inductively by applying a rule
whose premises all have finite derivations. It is the least fixed point of
the immediate consequence operator, and it is contained in every predicate
closed under the rules. A derivation tree can be a separate witness type if
the client needs to inspect it. Fix the interpretation of side conditions in
each presentation. Negative premises about derivability would require a new
semantics and new transfer results.

A shape map `f : Σ → Τ` has functions `fS, fL, fJ` satisfying
`fJ (edge e) = edge (fS × fL × fS e)`, where the product map sends both
endpoints and the label. It acts elementwise on rule premises and on the
conclusion. A strict presentation arrow `(Σ,R) → (Τ,Q)` is such a shape map
with `mapRule f r ∈ Q` for every `r ∈ R`. Identity uses identity functions
and composition uses function composition and successive rule preservation.
Extensionality on the three functions and proof irrelevance give the category
laws. Induction on derivations gives
`Derives R j → Derives Q (fJ j)`. One can later allow each image rule to be
*admissible* in the target, meaning that its translated conclusion is derivable
whenever all the translated premises are derivable. Identity and composition
then use derivation transport and the admissibility hypotheses. Keep this as a
second choice of arrows because it admits more maps.

For the functor to operational systems, send the shape to `(State, Label)`
and the model to `fun e => Derives R (edge e)`. Derivation transport supplies
`System.Hom.preserves`, and the shape maps give the functor laws. This can be
packaged as a `System F` over SOS shapes, with a further functor to
`TransitionSystem` that projects the two carrier maps. The latter projection
can identify distinct maps on auxiliary judgments. Even when judgments are
just edges, it need not be full: a rule `x ⇒ y` without any facts induces the
empty relation, so the identity step map to the empty presentation has no
strict rule lift.

For a Wasm conformance slice, use a unit-labelled ground presentation over Core
configurations, with auxiliary judgments only where needed. Prove
`Derives R (edge (s, (), t)) ↔ Step P host s t` for a declared domain. For a
full predicate equality on that domain, the encoded system then has inverse
step-preserving maps by `encode` and `decode`. If the domain is a fragment,
first give an induced or guarded target system and prove closure or specify
crossing edges. A scalar division rule plus its evaluation and trap contexts
is enough to test the comparison. Add finite observations via `Result`
separately. A Python-to-Wasm simulation would need a representation relation,
entry and host hypotheses, and a comparison of observations. In particular,
Python integers are unbounded and Wasm `i32` addition wraps.

For the policy view, project `step(s,t) := ∃ l, edge(s,l,t)` and supply
initialization and endpoint classification explicitly. With the same
observation type, a strong state map preserving endpoint observations and UB
induces an `OpSim` on its graph. Graphs compose by relational composition,
as in `OpSim.trans`. If observation payloads change, first align them with
`WithUB.mapObservations`. In the other direction an `OpSim` can match a
step with zero steps and can relate multiple states. It supplies neither a
map of labelled edges nor infinite-run transport. Strengthen it with a
progress argument for stuttering, labelled path matching and terminal
adequacy when those observations matter. [Simulation laws](../../Silmaril/Semantics/Operational/Policy/Thms.lean)

## An institution for SOS judgments

Use the category of shapes as signatures. Over `Σ`, a model is a predicate
on its judgments, with a discrete model category. Sentences are named
judgments `j` and finite clauses `[j₁,…,jₙ] ⇒ j`. Satisfaction is predicate
membership for atoms and material implication from membership of every premise
to membership of the conclusion for clauses. A presentation is a theory of
those clauses, with `Derives R` its least model. A theory arrow can be checked
by translated clause entailment. The category of concrete presentations above
has an explicit rule preservation condition.

For `f : Σ → Τ`, translate the names and clause entries with `fJ`, and
reduce a target model `M` by `M ∘ fJ`. Then
`SatΤ M (map f φ) ↔ SatΣ (reduct f M) φ`: for a clause, the two sides
quantify over the same list positions. Show identity and composition for name
maps, sentence maps and reducts. Use the existing
[`atomicInstitution` and `Fragment.atomic`](../../Silmaril/Logic/Fragments/Institution/Thms.lean)
when their sentence fragment suffices. For dedicated finite clause syntax,
build `Room.{u,u,u}` using Mathlib `Discrete`, matching the operational
institution's room universes. [`Builders.Plain`](../../Silmaril/Logic/Inst/Builders/Core/Defs.lean)
is another builder, with model hom universe zero. Comorphism builders require
matching sentence and model category universes, so use one discrete
representation across the intended link or explicitly lift it.

Concretely, [`ClassicInstitution`](../../Silmaril/Logic/Institution/Basic.lean)
has `Sen : Sign ⥤ Type` and `Mod : Signᵒᵖ ⥤ Cat`. In the bundled
[`Inst`](../../Silmaril/Logic/Institution/Morphism.lean), `I : Sign ⥤ Room`
packages these as corridors with sentences forwards, model functors backwards
and satisfaction in both directions. The shape projection gives an
`Inst.Hom` **from SOS to Operational**: `η : Φ ⋙ I_Operational ⟶ I_SOS`
translates an edge sentence into the SOS atom named by `edge`, and takes an
SOS model to its restriction to edge atoms. The square for each signature map
is the shape map's edge equation. The edge-only shape embedding gives an
`Inst.CoHom` **from Operational to SOS**: it sends each edge sentence to
its named atom and reduces SOS models by restricting to edges. The shape
projection composed after this embedding is identity on operational
signatures. On edge-only SOS signatures with atomic sentences, model and
sentence comparisons are equivalences.

Least models need care under change of signature. A target-only fact `z`
and rule `z ⇒ a` can make visible `a` true in the target least model. The
source with no rules has an empty least model. Predicate reduct is still
well-defined and preserves truth of translated sentences, but it is not
generally the least model of a pulled-back presentation. Run sentences also
need care: a target path between mapped endpoints can pass through an
unmapped intermediate state. For a native reachability equivalence require
path lifting, including endpoint and observation readback. For negative or
universal native run sentences, also account for maximality, divergence and
fairness as applicable. Alternatively `Plain.ofSat` translates arbitrary
predicates by reduct precomposition, giving an observational institution whose
translated predicates may differ from the target's native run sentences.

## SOS with a UB marker and with completion

In the marker variant, extend the signature with distinguished `ub : State →
Judgment` and require shape maps to commute with that naming. A model derives
or supplies the UB judgments. A strict model hom preserves UB and ordinary
edges; if entries and endpoint observations are tracked, require their forward
preservation as well. For a first implementation use freely tagged atoms
`Step(s,l,t)`, `Init(p,s)`, `End(s,o)`, and `Ub(s)` with common carriers
and componentwise maps. The ordinary signature has the first three tags. The
existing `Outcome` can encode return and uncaught exception with
`Except Error Result` in the payload, and has a separate trap constructor.
A missing entry, internal stuckness, waiting, and bounded-executor fuel
exhaustion each need their own status or observation policy.

On interpreted systems, forgetting `Ub` is a functor `U`, preserving all
raw steps, finite paths and endpoint observations. The embedding `E` adds
the empty marker, as in `WithUB.ofOpSem`; `U E = id`. With the forward
homomorphisms just specified, `E ⊣ U` since preservation of an empty marker is
automatic. `E` is fully faithful. `U` is faithful but can turn a function
that fails marker preservation into an ordinary homomorphism. Dropping the
marker at the rule level can change ordinary derivations if a rule uses it as a
premise. The interpreted forgetful functor avoids that problem. Preservation
of marker reachability under forward maps gives reflection of safety;
preservation of safety needs marker readback along all relevant target paths.

For the tagged institutions, the identity on underlying carriers gives an
ordinary-to-marker comorphism, translating old sentences by inclusion and
reducing target models by forgetting the marker. It is model-expansive via
the empty marker and has satisfaction equivalence for all ordinary clauses
and atoms. The marker-to-ordinary morphism can use the same inclusion of old
sentences and model forgetful map. No satisfaction equivalence for general
marker sentences follows from erasure: otherwise two models with the same
ordinary reduct and different `Ub(s)` would agree on that atom. The naturality
checks for these comparisons are commutation of the inclusion with name maps
and commutation of forgetting with predicate pullback.

The completion interpretation is a separate observation policy. Let
`Cut(p)` contain the finite paths from an entry for `p` whose last state
is the first marked state. For each such path `c`, let `Ext(view c) ⊆ Ω`
contain all complete observations with the same visible event prefix. The
completed behaviour set is the observations of marker-free maximal runs
unioned with `⋃ c ∈ Cut(p), Ext(view c)`. An implementation may start with
a coarser per-entry policy, `Ω` if any entry can reach a marker and ordinary
maximal behaviour sets otherwise. Use marker priority at a state that is
also a potential endpoint, or enforce disjointness. On starts
from which no marker is reachable, raw and completed behaviours coincide.
By construction completed behaviours can add returns, exceptions,
divergence or other observations. A completion erases which of those
behaviours were caused by a marker. It can commute with reduct only under an
appropriate observation and prefix lifting condition. For instance, if the
target has a path from the image of a start to a marker outside the image,
completing it can add outcomes even though reducing the raw model first
gives a safe start. An institution over completed observation predicates can
use pullback of observations as its reduct. Relating that institution to
primitive SOS needs a naturality and satisfaction proof. A forward simulation
with one-way inclusion supports the universal property transfer below.
An observation-level system arrow with input and observation maps must
explicitly preserve membership in the completed sets. Strict raw steps and
marker preservation alone give no such arrow for maximal observations.

## Python support and precision

Fix a contract before comparing profiles: a Python language release and the
subset under consideration, the built-ins and environment policy, a common
set `P` of core programs with inputs, initialization, and the observations.
For the first slice use a closed core AST, one initial state per admitted
input, mathematical integers, and no host calls or resource bounds. Treat
concrete CPython version, hash seed, float policy, implementation-dependent
identity, OS and resource behavior as distinct parameters for larger slices.
A comparison across those parameters needs its own translation or proof.
[Python language reference, expressions](https://docs.python.org/release/3.12.13/reference/expressions.html)

Let `Ω` be a common type of projected maximal-run observations. For a labelled
model, collect finite visible traces with a final classification (normal return,
uncaught exception, trap, stuck or externally blocked), and infinite-step
runs with a divergence tag and their finite or infinite visible trace. Keep
the divergence tag even if the infinite run produces finitely many visible
events. Specify the projection of silent steps and any observed final store.
A complete finite run ends at a designated stop, or at a state without
successors classified by the endpoint policy. Give designated stops priority
or prove terminal discipline. For the finite-only view, use just the chosen
outcomes and make the weaker claim explicit. Fuel exhaustion is a prefix of a
bounded search. In a fragment with rejection, record entry coverage separately
from the resulting behaviour set.

Profiles use the same core signature and state space, or provide explicit
program translations, a relation between initial and reachable states and
maps into the same `Ω`. Require coverage of each relevant concrete start.
An analysis over a concrete observation can be transported along a projection
`π` only if it follows from the predicate checked on `π(o)`. Equality of
user-visible behaviour is a stronger claim requiring readback. A noninjective
state map can splice paths, as documented by `WithUB.push`; state quotienting
needs the corresponding `Compatible` or other readback proof.

* **Feature support** is set inclusion on declared features, `F ⊆ G`. An
  admission predicate or rule subset alone may remove paths. A sound
  abstraction replaces the unresolved continuation at the first unsupported
  operation with overapproximating behaviours.
* **Precision** is `B ≤ A ⇔ ∀ p : P, B(p) ⊆ A(p)`, with the smaller
  behaviour set more precise. For a shared reference execution model, a
  sufficient condition for `B_G ≤ B_F` when `F ⊆ G` is that both agree with
  the reference before their first unsupported operation, every omitted
  operation on a concrete or abstract progression is intercepted by the
  boundary, and every observation permitted by the later cut extends an
  allowed suffix at the earlier cut. In the per-entry variant it suffices
  that reaching an unresolved operation for `G` implies the same for `F`,
  with exact common behaviour at entries resolved by both. Prove these
  hypotheses for each profile construction. For the prefix construction,
  induct along the reference path up to the first cut for `F`. Each
  observation of `G` either stays exact for `F` or belongs to the suffix
  set at that cut, by prefix compatibility. Strictness needs a witness
  `p, o` with `o ∈ B_F(p)` and `o ∉ B_G(p)`.

The abstract carrier `P → Set Ω` with this pointwise order is a complete
lattice. Arbitrary meets are intersections, joins are unions, and bottom and
top are the constant empty and universal sets. This carrier allows
inconsistent, non-realizable, or impossible assignments. Even restricting to
nonempty behaviours on all entries can remove binary meets (disjoint
singletons). Unions of singleton result behaviours can violate determinism.
Concrete well-formed Python profiles and chosen rule schemas therefore need
their own closure proofs. All sets of rules over a fixed carrier form a
complete lattice by rule inclusion, but least derivability is merely monotone
for that order. If one system has fact `a` and another has `a ⇒ b`, their
union derives the new `b`. If two systems derive `b` via disjoint rules,
their rule intersection can lose that common consequence. For a single fixed
positive theory, closed predicates form a lattice with intersections and
the closure of unions. With arbitrary ground axioms every judgment predicate
can be presented, which says nothing about realizability by well-formed
Python rules or about correlations across programs. The repo's
`WithUB.Included` and primitive pointwise meet/join compare steps, endpoints
and markers. [`WithUB.Permits`](../../Silmaril/Semantics/Operational/Determinism/Defs.lean)
orders ordinary relations forwards and immediate UB backwards.
[`enforce_permits`](../../Silmaril/Semantics/Operational/Determinism/Thms.lean)
gives `(M.enforce goodG).Permits (M.enforce goodF)` when
`goodF s → goodG s`. It is a primitive policy comparison. Adding an edge
to an already marked state can introduce reachable UB even with the same
immediate marker sets, so `Permits` alone gives no completed-behaviour
precision claim. `WithUB.SafeRefines` uses safety of the specification as a
premise, while `HasOpSem.Refines` asks for unconditional finite-may inclusion
and no new reachable UB. These API orders have different laws from the
maximal-observation lattice above.

### Transfer and example

Let `C` be the reference model and `A` an abstraction on the named input.
Assume an entry exists for the reference, all its starts are covered, and
every reference maximal run under the fixed environment projects to an
observation in `B_A(p)`. For a demonic UB-free claim additionally prove
`∀ s, initial_C p s → SafeAt_C s`. This follows from safety of the matched
abstract starts when the simulation also preserves UB reachability in that
direction. Then `(∀ o ∈ B_A(p), Q o) → ∀ r, MaxRun_C p r → Q (π r)` by
membership and application. With completed behaviours the set argument
still holds at unsafe inputs if inclusion is proved there, though properties
can be lost to the larger set. Under a proof of safety, a marker completion
does not change the corresponding model's run observations. To prove a
nonvacuous universal result, also establish existence of a maximal run
under the selected environment or obtain it directly for the slice.

Finite may-outcome inclusion alone admits a source loop and a target that
returns, even with an empty-step simulation to the target's start. It also
misses a branch that is stuck while another returns. Even step inclusion can
turn a source dead end into a nonmaximal target prefix. With **maximal**
observations and coverage of all source runs, universal termination can
transfer if the predicate excludes divergence, stuckness and waiting and
requires the intended terminal status. A nondeterministic abstract return
does not witness a concrete return. Existential or angelic claims need a
concrete witness or the reverse inclusion for the relevant observation.
With fairness, inclusion must hold for projected source-fair runs in the
target's chosen fair set. Dropping labels or inserting stuttering can change
fairness, and a fair-execution claim may additionally require fair-run
existence. Compare observations at the same host assumptions.

Use a closed core body returning `2 + 5` on exact integers. The expression
reduces by integer addition, then the statement emits the return. The supported
profile has only return 7 once adequacy and progress are proved. A profile
without the addition rule meets an unsupported operation before any visible
effect. Its completed set includes return 7 and return 8, witnessing the
strict precision comparison. If it only drops the rule, the result can be
stuck and the finite return set empty. As a negative control, integer floor
division by zero raises `ZeroDivisionError` under a profile that implements
it. An unsupported division operation may be intercepted as an analysis
boundary. These are distinct classifications, as is Wasm integer division's
defined trap. [Python language reference §6.7](https://docs.python.org/release/3.12.13/reference/expressions.html#binary-arithmetic-operations)

## Implementation and acceptance

1. **One core body.** Put the relational core and labelled machine in
   `Silmaril/Languages/Python/Core/{Defs,Thms}.lean`, and keep longer proofs in
   the matching `Silmaril/Proofs/Languages/Python/Core/` topic. Use a small
   syntax of integer literals, exact addition and return, with an explicit
   exception form when testing effect propagation. Reuse CSLib finite runs
   and the existing `Labelled.Finishes` for finite visible logs where its
   `Option Label` silent/visible interface suffices. Provide `HasOpSem`,
   step determinism on reachable states, progress
   to classification, a termination measure, and an iff between finite may
   and the independently specified integer result. Prove no reachable UB on
   admitted starts and show a missing entry and an unsupported state are
   distinct. Prove an executable bounded runner sound if one is needed
   for regression. Then separately show sufficient fuel on the slice.
2. **Rules and the existing Wasm adapter.** Place finite positive rule
   closure, map and induction in `Silmaril/Semantics/SOS/{Defs,Thms}.lean`.
   Check for overlap with the existing
   [reachability derivation](../../Silmaril/Logic/Reachability/Derivation/Defs.lean)
   and [rule-scheme adapter](../../Silmaril/Logic/Reachability/RuleSystem/Defs.lean).
   The latter generates a binary reachability relation from valuations of
   left and right patterns. The SOS need here is mutually recursive positive
   judgment premises.
   Put signature-to-room and system functors in
   `Silmaril/Logic/Operational/SOS/{Defs,Thms}.lean`. Test a Python body
   through the same generic interfaces as the public Core `step_iff`
   adapter, with the candidate Wasm rule presentation in `Wasm`. Prove
   `rule_step_iff` independently of the typed Python step, functor laws,
   `sat_map`, the `Inst.Hom` naturality square, and a two-step labelled
   run mapping. Use a fixture importing both `Logic` and the Python core.
   `Languages` currently has no direct `Logic` or `Wasm` dependency.
   A Python-specific library institution importing `Logic` would require
   an intentional region dependency change or placement in a suitable
   downstream region.
3. **First precision proof.** In `Semantics`, prove the marker embedding,
   reuse `restrict_readback` and `SafeAt.of_reach` on the closed safe-state
   subtype, and prove the per-entry completion and set-inclusion transfer
   lemmas. In the Python fixture prove the exact
   supported result, show the wider unsupported profile admits it and one
   spurious result, and exercise an exception and a stuck state. Include
   counterexamples to unrestricted native reachability under reduct and to
   termination under may inclusion. Only extend to prefix-sensitive
   completion when a trace client can test it.
4. **Expand by proof boundary.** Take evaluation contexts, explicit
   primitive-service interfaces, and the expression–statement–frame–stack–
   memory decomposition as the design for larger slices. Demonstrate
   closure and action transport at each boundary. Defer source parsing and
   scope elaboration, bootstrap and object protocols, generators and host
   effects, symbolic search and compiler correctness until a client needs
   them. If adding a finite presentation for function-valued heaps, prove
   the action and successor projection both ways and thread the chosen
   residual witnesses to get a run theorem. Expand comparison to Wasm only
   with an explicit value, store, environment and observation contract.

For implementation PRs, put regressions under `tests/semantics/`,
`tests/languages/python/` and `tests/wasm/` as applicable. Build changed
headers and direct clients with `lake build --wfail`, run the new regressions
with `lake env lean -DwarningAsError=true`, and run the relevant
`make check CHECK_TARGETS=…` gates. Audit transitive axioms for the rules,
institution and transport theorems. Existing checks on the public interfaces
include the [operational-institution regression](../../tests/semantics/operational-institutions/Regression.lean)
and [policy regression](../../tests/semantics/operational-policy/Regression.lean).
The proposal adds no Lean implementation.

## Sources

* Maximilian A. Köhl, *An Executable Structural Operational Formal Semantics
  for Python*, December 2020, arXiv v1, chapter 3, §§4.3–4.4 and Appendix B.1.
  The thesis uses Python 3.7 as its baseline. The first slice uses the
  exact-integer and return fragment shared with the reference below.
  PDF SHA-256 `104b05eaa440d07e41787e2b6648ce5f066bcdd65d70178630da2933b8071221`.
  [Public PDF](https://arxiv.org/pdf/2109.03139v1)
* Python Software Foundation, *The Python Language Reference*, release 3.12.13,
  §§6.7 and 6.16. HTML SHA-256
  `d8c992b1815b59ba65aa9a0144bf2f0a24a3551cda8cbb06f5e76c5caec7d994`.
  [Expressions chapter](https://docs.python.org/release/3.12.13/reference/expressions.html)
* Institution definitions and variance follow Goguen–Burstall, §2.1 and §2.5,
  and Goguen–Roşu, §4. Exact public artifact references are recorded in
  [references.bib](../../references.bib).
