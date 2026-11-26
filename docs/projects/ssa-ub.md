# Free undefined behaviour in Isotope refinement

In the ordered institution, the inequation `a ⊑ b` is interpreted as
`⟦a⟧ ≤ ⟦b⟧`. In the observational institution it is inclusion of the
outcomes of `a` in those of `b`. UB, which permits every outcome, is on the
right of `t ⊑ ub`. A compiler contract can accordingly place the target on
the left and the source on the right. See [ordered satisfaction][ordered],
[observational satisfaction][obs], and [the compiler convention][compiler].

## Construction

The native term and region grammars have empty-type elimination. Literal UB
is introduced here through the extended presentation and the unit-fed
instruction spelling. [LetCase typing][case-typing] [LambdaSSA syntax][ssa-syntax]
[LambdaRTL syntax][rtl]

- `UB.dialectMonad e` acts on `InstrSig τ ε` for fixed types, effects, and UB
  effect `e`. A primitive has one typed input and one result. The new symbol
  at result type `A` has profile `unit → A` and effect `e`. A morphism
  extending a relabelling can choose any symbol with precisely that profile.
  The unbundled `SignatureMap` also changes types and effects. A corresponding
  lift needs to preserve unit and transport the chosen effect as well as the
  ordinary typing and effect premises. [Primitive extension][primitive]
  [Instruction morphisms][instr] [Varying signatures][sigmap]
- `UB.signatureMonad` acts on the contextual `PSig` used by the ordered
  institution. It adds a literal arity-zero operation per judgment sort.
  For LetCase and LetIter a sort includes a bound context and a result type,
  with the free-variable context fixed by the presentation. The independent
  explicit constructor `Expr.ub` has the unique fold into any algebra for
  the extended signature. [Explicit syntax][syntax] [Signature monad][signature]
- `UB.Specification.monad` acts on the institution's specifications. A map
  must send axioms to consequences. The extension transports the old axioms
  and adds `t ⊑ ub` for **every** term at its sort, including expressions
  under binders. `homEquiv` states the universal property for targets with
  designated nullaries above every denotable term. Restriction along the unit
  and extension using the designated symbols are inverse. In each monad the
  unit includes the old operations and multiplication identifies the inner
  and outer fresh symbols. In the ordered case the two symbols may still be
  distinguished before applying multiplication. [Specifications][spec]
  [Institutional consequence][institution]
- Monotone algebra operations place the inequalities under well-sorted
  constructors. The whole expression in any such context lies below UB at
  the result sort. An equation saying a context around UB evaluates to UB
  would need separate absorption laws. In arbitrary validating algebras the
  top rule bounds the image of the syntax fold. In the initial ordered
  quotient every element is represented by syntax, and `initial_le_ub`
  bounds the entire carrier at every sort. The ground inequations alone
  cannot constrain elements outside that image. `model_without_top` gives
  a two-point validating algebra whose carrier has no greatest element.
  [Ordered algebra and quotient][models]
  [Initial model][spec]

## Ordered LetCase bridge

`refinement_iff` preserves and reflects refinement between literal-unit
endpoints. `quotientIso` identifies the explicit quotient by mutual
refinement with the quotient of canonical native terms by the inherited
native order. The native presentation uses the full well-typed extended
dialect as syntax. Its generators are the relabelled original sentences and
`t ⊑ op (ub A) unit` for every native `t : A`. The proof uses monotone
constructor operations, retains the chosen primitive effect, and imposes no
purity requirement on it. Canonical elaboration always supplies literal unit,
so it never erases an effectful operand. Readback on arbitrary operands is
used internally to compare these generated axioms. [Bridge][case-refinement]

With the original sentences taken from `caseTheory`, `preserves_native`
also gives a derivation in LetCase's full native refinement calculus with
the transported primitive rules and the top rule. Reflection into the
original free extension fails for that stronger target. Native case beta
drops an unselected branch containing UB, even with effectful UB and
canonical endpoints. The Boolean occurrence model validates the interpreted
axioms and distinguishes the two terms. Its `true` is greatest and
`encode_eval` gives agreement with the induced explicit interpretation.
The flag includes both branches and describes UB occurrence in syntax.
[Model][case-model] [Checked counterexample][case-regression]

## Ordered LetIter bridge

LetIter's exact typing judgments have free and bound contexts and a result
type. They carry no usage quantities or effect bound. The literal-unit
round trip holds at each such sort, including the iteration body at
`β.snoc A` with result `B ⊕ A`. The chosen UB effect is preserved on
the native instruction. Readback is inverse on canonical terms, where
each fresh instruction has a literal unit operand. `refinement_iff` and
`quotientIso` compare the explicit and interpreted orders on those terms.
The latter is generated over the full native syntax by the relabelled
old sentences and a UB upper bound for each typed native term.
[Typed round trip][iter-ub] [Ordered bridge][iter-ub-refinement]

With inherited sentences from `iterTheory`, `preserves_native` embeds
the explicit order into the full native refinement rules. The checked
regression separates native fixpoint unrolling from the interpreted
axioms. Its two-point model ignores the iteration body when reading a
loop and reads the scrutinee when reading a case. The unrolling moves
the UB body into a scrutinee, so the native equation can give a
comparison the matched axioms do not entail. This model only witnesses
the algebraic separation. [Checked fixpoint example][iter-ub-regression]

Quantitative LetIter uses a separate typing judgment. At bound `b`,
`op (ub A) unit` typechecks exactly when `Γ.Discardable` and
`ubEffect ≤ b`. In the iteration rule, the ambient context `Γl`
already has `Γl.linearity = ⊤`. The body context `Γl.snoc A` is
discardable exactly when the incoming state's type admits discarding
(`Quantity.affine ≤ quantity A`). A linear state blocks literal-unit
UB in that body even at the top effect bound. The stable rewrite
presentation in `topRules` keeps formed endpoints under native
weakening and pure substitution. The comparison to literal UB holds
exactly for formed left endpoints in discardable contexts.
`typeIterLiteralBody` adds the ordinary iteration guard `iterable b`,
and `iter_body_refines_literal` uses native iteration congruence at the
original context split. [Quantitative typing and refinement][iter-ub-quant]

## LambdaSSA's empty-label boundary

In the exact LambdaSSA typing judgment, a region with no external labels
must contain a local block. `not_noLocalBlocks` excludes even regions that
wrap their bodies in zero-block CFGs. A unit-state CFG that branches to
itself gives a typed region at every value and label context. A unit-fed
instruction can be sequenced before that CFG, with the local backedge
ignoring its result. Exact LambdaSSA typing here has no quantitative
usage or effect-bound premise. [Typing][ssa-typing] [Witnesses][ssa-ub-defs]

`Refines` compares sets of return, fault and divergence observations by
inclusion in every model of the observational institution. In the
`faultModel` every primitive faults, with no successful primitive
transitions and no primitive divergence. The unit-fed prefix faults
and the bare CFG diverges. A simultaneous upper bound would need both
observations from the same initial state. Mutual induction through
nested CFGs and block traversal proves that fault and internal divergence
are exclusive when successful primitive steps are deterministic and a
faulting primitive call cannot also return. Thus `no_common_upper_bound`
and `no_greatest` hold for every exact typing interface of an alphabet
with a unit-taking operation. This includes the fresh `unit → A`
instruction in `UB.dialect P e`, for any effect label `e`. The obstruction
quantifies over all typed native regions, so it also bounds what can be
encoded using typed native substitution or feedback. [Observation order][ssa-observations]
[Obstruction][ssa-ub] [Dialect regression][ssa-ub-regression]

At a fixed model, an empty-label region has no finite return. Its
observations are contained in the set of all faults and divergences.
The unit-fed prefix attains that greatest set if its primitive can fault
from every initial state to every final state and can, at each initial state,
either diverge or return to the backedge. The regression instantiates this
with a model in which the instruction both faults and can diverge.
Greatest behaviour here is a law of that model. [Fixed-model result][ssa-ub]
[Model regression][ssa-ub-regression]

### Explicit region UB with substitution and feedback

The independent `Overlay.Region` embeds any exactly typed native region,
adds a UB region at every interface, and provides label substitution and
feedback. A continuation or block receives the exit payload in its own
value binder and retains the original captured context. Native regions may
contain arbitrary nested CFGs. [Overlay syntax][ssa-ub-overlay-defs]

For each observational model, bound environment and initial state, the
carrier is `WithTop (Set Outcome)`. An outcome carries a scoped exit and
payload, a fault state, or divergence. The refinement order is pointwise
subset on ordinary sets with a distinct greatest UB element. An ordinary
universal set stays ordinary. The projection back to native observations
recovers the original observations on every native region, and the embedding
preserves and reflects the original refinement preorder. [Conservativity][ssa-ub-overlay]

`lsubst_mono` proves directed congruence in the source and all continuations.
Sequencing propagates source faults and divergence and runs continuations
only on successful exits. UB in the source or a reached continuation lifts
the whole behaviour to greatest at that initial state. Substituting into UB
preserves UB even when the target has new labels. For all-native inputs,
`denote_native_lsubst` proves exact agreement with one typed dispatch CFG
whose blocks run the continuations, including faults, external divergence,
and internal divergence of the existing native regions. [Substitution laws][ssa-ub-overlay]

Using ordinary universal outcomes as UB would lose this absorption law.
An empty label interface has no successful exit, so ordinary sequencing
cannot turn even its universal set into a return at a target label.
The regression uses a native region that already has all empty-interface
outcomes in one model. Its ordinary projection equals the projection of
explicit UB at the source, yet their substituted projections differ at a
single-exit target. Thus ordinary outcome equality at a fixed model is
insufficient for a compositional interpretation with both native sequencing
and absorbing UB. The lifted order retains precisely the distinction used
in this counterexample. [Checked obstruction][ssa-ub-overlay-regression]

Feedback splits the outgoing interface as `R ++ L`. An ordinary return to
`R` invokes the corresponding local block with the returned payload and
machine state. A return to `L` exits. Fresh top occurs exactly when a finite
path of ordinary internal returns reaches a component at fresh top. Below
top, finite paths collect external returns and faults, and divergence comes
from a finitely reached component divergence or an actual infinite
sequence of internal returns. `feedback_mono` proves directed congruence
in the entry and all blocks, including refinements that expose UB earlier.
The top and ordinary parts also satisfy one-step unfolding.
[Feedback laws][ssa-ub-feedback]

For native entry and blocks, `denote_native_feedback` agrees with the
repository's typed recursive CFG at every existing observational model.
The regression checks a block whose first visit takes a backedge and whose
second visit reaches UB, an immediate exit that bypasses a UB block, and a
native self-loop whose divergence is absent from finite closure.
[Native agreement][ssa-ub-feedback] [Regressions][ssa-ub-feedback-regression]

Feedback uniformity compares two graphs with the same external interface.
The local theorem assumes that at each reachable source point, a
deterministic point map sends each source step to a target step and lifts
every step out of the image to a source successor with that exact image. The matched points must agree on
fresh UB and ordinary external returns, faults, and divergence. These
conditions are required only on reachable source points. They preserve and
reflect finite paths, reached UB, and actual infinite paths. The reverse
infinite proof lifts the selected target path one step at a time, choosing
a source successor at each step. The exact criterion for equality of
closed behaviours is agreement on whether UB is reachable and, below UB,
equality of the resulting ordinary outcome sets. [Uniformity][ssa-ub-uniformity]

A type-preserving label map keeps payloads and machine states and may merge
labels of the same type. `close_slide` proves the deterministic routing
instance of the Conway sliding law. Closing a body with routing on its
block inputs gives the same behaviour as closing it with routing on its
internal returns. Permutations give block relabeling invariance as a
corollary. The one-way counterexample preserves local marks and ordinary
outcomes on reached source points, yet a new target edge can expose UB or
enable infinite replay.
[Sliding and relabeling][ssa-ub-uniformity] [Checked counterexample][ssa-ub-uniformity-regression]

Two-level elimination views the same overlay semantics as a graph of
ordinary transfers, local UB and terminal observations. The graph's
one-shot closure agrees definitionally with `Feedback.close`. Closing
the inner group exposes each transfer to an outer point as a boundary
outcome, carrying the label, payload and machine state. The outer closure
consumes these boundary outcomes. `close_two_levels` proves equality
with the flat closure for the typed hidden interface `I ++ O`.
`close_partition` allows any partition of the invocations.

Finite paths split at outer visits. An outer step consists of zero or more
inner transfers and a final original edge into an outer point, so every
such step consumes at least one original edge. If a reachable inner UB
suppresses an otherwise available boundary transfer, the outer closure
already has a witness to UB. Below UB, the finite terminal comparisons
retain the original outcomes.

For a selected infinite flat path, either all visits after some index
are inner, or a later outer visit exists after every index. The proof
in the first case uses the finite prefix to reach the final inner replay.
In the second case `Nat.find` selects the least next outer visit, so the
intervals between selected visits are finite inner segments. In reverse,
an inner replay can be prefixed by the finite flattened outer path.
An infinite outer replay provides nonempty flat segments. Classical
choice selects a real successor at each original step, maintaining a
finite suffix to a segment boundary. The regressions exercise both kinds of
replay, a finite external outcome, and early UB in an inner segment.
Full Conway and Elgot laws remain open.
[Elimination theorem][ssa-ub-elimination] [Regressions][ssa-ub-elimination-regression]

### Descent through the native CFG entry quotient

`cfgDenotation` lifts the map `r ↦ denote (.native r)` through the
installed `Region.CfgQuotient` at each exact value and label interface.
`cfgEquiv_obs` covers empty CFG elimination, an outward entry branch,
and unfolding a local entry branch into its block. It uses the existing
observational congruences for lets, cases, and CFGs and preserves returns,
faults, and both sources of may-divergence in every observational model.
The descended map supports overlay substitution and recursive CFG assembly.
Semantic relabeling and two-level elimination apply to feedback over the
resulting quotient denotations. [Native quotient][ssa-cfg-quotient]
[Descent][ssa-ub-native-quotient]

The guarded `Paper.Hom` and the native `ContinuationHom` admit checked
counterexamples to the same representative contract. Paper's product η
identifies a split and rebuild with a direct return. A bound value of unit
at the product-typed input makes only the direct return succeed. Native
initiality identifies a return with an empty-typed elimination, which
the same model separates when it supplies unit at an empty-typed input.
Both witnesses have constructor-valued branch arguments and use no
primitive transitions. The observation model indexes bound values by scope
and imposes no payload shape. Shape-aware environments would exclude
these witnesses. The installed categorical soundness theorem for Paper
uses a coherent typed region denotation and its stated categorical
hypotheses. [Paper soundness][ssa-paper-soundness]
[Obstructions][ssa-ub-descent-obstruction]

The regressions check one UB-producing branch of a nondeterministic
producer, an outward CFG entry that bypasses blocks leading to UB after
substitution, and a local entry unfolding whose infinite replay remains
ordinary divergence. The outward example also checks semantic relabeling
and staged feedback on the native quotient inputs.
[Descent regressions][ssa-ub-descent-regression]

## Coverage and gaps

| Language | Refinement and institutions in the repository | UB construction and remaining hypotheses |
|---|---|---|
| LetCase | The exact typed preorder gives `caseTheory` and ordered algebra models. The separate operational institution observes results, faults and divergence. | Instantiate the ordered monad with `casePSig` or the specification of `caseTheory`. `typedEquiv` proves both typed round trips between explicit UB and native terms generated with `op (ub A) unit`, including under binders. The interpreted order preserves and reflects on these endpoints. Arbitrary unit-typed operands can have effects, and an operational equivalence needs to preserve their evaluation and justify the sequencing and UB laws in the chosen observation model. [Ordered theory][let-theory] [Typed round trip][case] [Ordered bridge][case-refinement] [Observations][obs] |
| LetIter | `iterTheory` gives ordered refinement models. The separate quantitative `Refinement.Thms` also has categorical initiality and singleton-input completeness. Operational stuckness yields an undefined outcome, while the observational institution tracks returns, faults and divergence. | The exact literal-unit round trip and ordered quotient comparison include the iteration binder. Quantitative literal-unit UB is limited to discardable contexts and compatible effect bounds. A linear input would require a resource-consuming encoding or a different typing rule for UB. [Ordered theory][let-theory] [Ordered bridge][iter-ub-refinement] [Quantitative typing][iter-ub-quant] [Categorical initiality][quant] [Undefined outcome][iter-beh] |
| LambdaSSA | Typed terms use unary instructions and regions have separate value and label contexts. The CFG entry quotient uses `CfgEquiv`. The continuation quotients install additional equations. The observational institution has inclusion of outcomes, with an observational isomorphism to LetIter for single-exit regions. | The primitive monad supplies a unit-taking expression instruction. Every exact typing interface, including the empty-label boundary, has a countermodel to uniform greatest refinement by a native region. At a fixed model with the stated saturation assumptions the unit-fed prefix is greatest at the empty interface. The independent exact-typed overlay adds a distinct greatest element with monotone substitution and feedback, each with exact all-native CFG agreement. The overlay denotation descends through the native CFG entry quotient. The larger continuation quotients need a stronger observation model. [Native descent][ssa-ub-native-quotient] [Empty-label boundary][ssa-ub] [Explicit overlay][ssa-ub-overlay] [Feedback][ssa-ub-feedback] [Typing][ssa-typing] [Rewrite quotient][ssa-rewrite] [Observational isomorphism][ssa-obs] |
| LambdaRTL | The acyclic model interprets unary applications in a monad; its alphabet institution takes the observation relation as a parameter. It distinguishes lexical SSA, projected RTL and full RTL store observations. The separate machine RTL adapter reports stuckness as an undefined outcome. | A top region needs a chosen store/label observation order and a typed result and continuation interface. Its interpretation must dominate all observations for every environment at the selected boundary. An instruction relabelling or a lawful monad supplies no such law. [Syntax and model][rtl] [Institution][rtl-inst] [Machine RTL outcomes][rtl-beh] |

An effect bound of `⊤` permits all effects in the typing system. It does
not establish that any computation is greatest. The effect used for a fresh
primitive remains a parameter, and assigning the pure effect would also
invoke existing purity obligations. For a
behaviour-set model one can ask for the existing convention exemplified by
MIR's `ubClose_of_undefined`, which yields the universal outcome set.
Neither the monadic model interfaces nor weak interaction-tree equivalence
provide that UB order or its sequencing laws. [Effect system][effects]
[Empty elimination][quant-typing] [MIR UB closure][mir] [Kleisli model][kleisli]
[Weak-tree semantics][weak-tree]

## Checks

```sh
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Refinement.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Regression
```

[ordered]: ../../Silmaril/Raw/SSA/Isotope/Institution/Refinement/Ordered.lean
[obs]: ../../Silmaril/Raw/SSA/Isotope/Institution/Observational/Basic.lean
[compiler]: compiles-to.md
[primitive]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Primitive/Thms.lean
[instr]: ../../Silmaril/Raw/SSA/Isotope/Institution/InstrSig.lean
[sigmap]: ../../Silmaril/Raw/SSA/Isotope/Morphism/Instructions/Signature.lean
[syntax]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Syntax/Defs.lean
[signature]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Thms.lean
[spec]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Specification/Thms.lean
[institution]: ../../Silmaril/Logic/Institution/Theory.lean
[models]: ../../Silmaril/Raw/SSA/Isotope/Logic/Metatheory/Theory/OrderedModel.lean
[case-typing]: ../../Silmaril/Raw/SSA/Isotope/LetCase/LocallyNameless/Typing.lean
[ssa-syntax]: ../../Silmaril/SSA/Isotope/LambdaSSA/Defs.lean
[case-refinement]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Refinement/Thms.lean
[case-model]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Model/Thms.lean
[case-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Refinement/Regression.lean
[case]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Thms.lean
[let-theory]: ../../Silmaril/Raw/SSA/Isotope/Institution/Refinement/Isotope.lean
[iter-ub]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Thms.lean
[iter-ub-refinement]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Refinement/Thms.lean
[iter-ub-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Regression.lean
[iter-ub-quant]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetIter/Quantitative/Thms.lean
[quant-typing]: ../../Silmaril/Raw/SSA/Isotope/Refinement/Typing.lean
[quant]: ../../Silmaril/SSA/Isotope/Refinement/Thms.lean
[iter-beh]: ../../Silmaril/Raw/SSA/Isotope/LetIter/Semantics/Behaviour.lean
[ssa-typing]: ../../Silmaril/SSA/Isotope/LambdaSSA/Typing/Defs.lean
[ssa-rewrite]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Syntactic/Defs.lean
[ssa-obs]: ../../Silmaril/Raw/SSA/Isotope/Institution/Observational/Isomorphism.lean
[rtl]: ../../Silmaril/SSA/LambdaRTL/Defs.lean
[rtl-inst]: ../../Silmaril/SSA/LambdaRTL/Institution/Defs.lean
[rtl-beh]: ../../Silmaril/Raw/Machine/RTL/Behaviour.lean
[effects]: ../../Silmaril/Raw/SSA/Isotope/Refinement/Effects.lean
[mir]: ../../Silmaril/Raw/Compiler/Mir/Semantics.lean
[kleisli]: ../../Silmaril/SSA/Isotope/LetIter/Categorical/Kleisli/Thms.lean
[weak-tree]: ../../tests/ssa/LetIterWeakTreeSoundness.lean
[ssa-observations]: ../../Silmaril/SSA/Isotope/Institution/Observational/Thms.lean
[ssa-ub-defs]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Defs.lean
[ssa-ub]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Thms.lean
[ssa-ub-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Regression.lean
[ssa-ub-overlay-defs]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Defs.lean
[ssa-ub-overlay]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Thms.lean
[ssa-ub-overlay-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Regression.lean
[ssa-ub-feedback]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Thms.lean
[ssa-ub-feedback-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Regression.lean
[ssa-ub-uniformity]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Uniformity/Thms.lean
[ssa-ub-uniformity-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Uniformity/Regression.lean
[ssa-ub-elimination]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Elimination/Thms.lean
[ssa-ub-elimination-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/Feedback/Elimination/Regression.lean
[ssa-cfg-quotient]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Syntactic/Defs.lean
[ssa-paper-soundness]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/Soundness/Thms.lean
[ssa-ub-native-quotient]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/NativeQuotient/Thms.lean
[ssa-ub-descent-obstruction]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/NativeQuotient/Obstruction/Thms.lean
[ssa-ub-descent-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LambdaSSA/Overlay/NativeQuotient/Regression.lean
