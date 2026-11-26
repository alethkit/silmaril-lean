# Packed execution of normalized φ-SSA

## Finite returns

A finite return of the predecessor-indexed source semantics is equivalent to
finite evaluation of the accepted Isotope elaboration. The translation first
uses the checked φ lowering and then elaborates its exact lexical CFG with
`NamedFlat.elaborate`. Each positional capture must agree with the source
input at the corresponding lexical name. Both evaluators use the same tagged
values and the same stateless partial primitive implementation. The explicit
`none` return label is the only external label, so its exit index is zero.
[φ lowering](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Thms.lean) · [Finite bridge](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Thms.lean) · [Named lexical correspondence](https://github.com/hiloopai/silmaril-lean/pull/3396)

The packed theorem additionally requires exact typing of the closed graph and
a capture-closure witness for the accepted elaboration. The capture producer
must evaluate to exactly the original capture record with unchanged state.
The packed evaluator reports a tagged return at its single exit. The named
adapter checks the supplied typing profile and restricts the supported
primitive syntax. [Capture closure](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Capture/Thms.lean)

The regression exposes the numeric countdown through a typed sum-producing
classifier and closes four captures. The packed evaluator observes the
backedge swap of `2` and `5`, including the latch's ordinary live-in, and
rejects the sequential-assignment result. The mutable correspondence also
applies to the intermediate tuple-argument CFG produced by `Phi.lower`.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Examples.lean) · [Mutable correspondence](https://github.com/hiloopai/silmaril-lean/pull/3415)

Normalized φ inputs require one edge per source-target pair. [φ interface](lambdassa-theorem-crosswalk.md#conventional-φ-nodes-and-block-arguments)

## Atomic infinite paths

A source infinite path starts with a successful entry and continues with a
successful internal transfer at every index. The local correspondence reflects
each successful lexical entry and continuation to a source transfer with the
same encoded packet. The lifted path retains the predecessor and store for
the next φ assignment. [Local transfer theorems](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Infinite/Thms.lean)

The same accepted elaboration, shared stateless partial primitives, capture
agreement, exact packed typing and state-preserving capture packet give an
equivalence with atomic packed divergence. The repeating classifier in the
typed regression takes the backedge and keeps swapping unequal values. The
stuck classifier fails before the first internal successor. Both source
runners return `Part.none`, and only the repeating classifier gives a source
path or packed divergence. [Infinite bridge](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Infinite/Thms.lean) · [Named atomic divergence](https://github.com/hiloopai/silmaril-lean/pull/3443)

## Global SSA admission

The optional certificate gives a finite set of names available on arrival at
each named block, before its φ destinations are defined. The entry starts
with the declared inputs. The checker reads each ordinary operand before
its instruction's definitions and checks each case arm with its own payload
binder. A φ operand is read at the selected predecessor's terminator. Each
internal route must justify its successor's arrival claims. [Checker](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/WellFormed/Defs.lean)

A passing certificate proves unique static definitions, including declared
inputs and binders in unreachable blocks. Every read on every syntactic
entry path has an earlier definition or a declared input. This covers
same-block order and dominance across blocks. The certificate must cover
every reachable target. It can omit unreachable blocks, and weak arrival
claims can cause rejection. The regressions admit a loop-carried operand and
reject a sibling branch's payload on the wrong φ edge, a same-block forward
read, and a duplicate static definition. [Soundness](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/WellFormed/Thms.lean) · [Regressions](../../Silmaril/Proofs/SSA/LambdaRTL/CFG/Cyclic/Phi/WellFormed/Examples.lean)

`GlobalSSA.compile` adds that source guarantee to the result of
`Phi.compile`. The original compiler and its entry, transfer, and run
theorems still require only the structural φ admission and their stated
model assumptions. Primitive and value typing, typed Isotope admission,
and capture agreement are separate obligations. [Source semantics](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Thms.lean) · [Typed admission](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Thms.lean)

## Visible interaction trees

`NamedFlat.Phi.runTree` runs the original predecessor-indexed evaluator in
the shared weak ITree model. It evaluates every selected φ operand against
the predecessor's outgoing store and commits the φ assignments in parallel before the
target body runs. The lexical packet encoding commutes with entry and the
continuation of every step, including stores reached after primitive replies.
Weak-tree iteration lifts those equations to the whole run. [Local and whole-run equations](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/ITree/Thms.lean)

The open bridge uses the actual accepted elaboration with matching entry
captures. The packed bridge also requires exact closed typing, a
capture-closure witness, and a capture expression that runs the supplied
producer and packs the capture environment for each reply. Both use the
same primitive trees. The external list is `[none]`, so an explicit return
occupies slot zero and receives the corresponding packed tag.
[Named elaboration](https://github.com/hiloopai/silmaril-lean/pull/3473) · [Effectful capture closure](https://github.com/hiloopai/silmaril-lean/pull/3495)

The bridge accepts the original structural lowering equation. The regression
supplies it through `GlobalSSA.compile_sound`, and uses `compileTyped` and
`Capture.close` for the checked target. The producer's reply supplies the
first tick operand. A continuing tick reply is bound on the self-edge and
becomes the next request's operand through the φ node. Either tick can
return through the packed exit. The equation is in weak ITrees. The finite
and infinite atomic results above are stated in `Part`.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/ITree/Examples.lean)

## Checked admission and closure

`Certified.admit` runs the global SSA checker and the typed elaborator in
sequence. The source witness establishes normalization, definition uniqueness
and use availability. The target witness supplies its exact elaboration and
typing at the given capture, block and return profiles. An admitted result can
run `admitted.close` with a closed expression of the packed capture type.
Successful closure supplies the closed graph's typing and its erasure relation
to that same admitted graph. [Checked results](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Defs.lean)

The end-to-end theorems consume the result of closure. They recover the
lowering, elaboration, typing and closure premises from the returned evidence.
The positional capture environment is derived from the source store and
the selected version-zero names. The remaining semantic premise is that the
capture expression produces exactly this record. In weak ITrees it runs the
supplied producer, then packs the source store for each reply. In the atomic
`Part` theorems it returns the record with unchanged state. In each case both
sides use the same primitive implementation.
[End-to-end theorems](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Thms.lean)

The visible backedge regression uses these checked outputs directly. A wrong
Isotope return type rejects the same graph with its valid source certificate.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/ITree/Examples.lean)

## Canonical pure capture

`Certified.PureCapture.close` takes the existing admission and synthesizes
its closed packet expression. The target signature adds an input read for
each finite capture slot, with the slot's type from the admitted profile.
The generated expression supplies unit to each read and assembles the same
newest-on-the-right product as `packedInputType`. The original graph's
operations retain their signatures and interpretations. [Generator](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Defs.lean)

The slot interpreter reads the existing version-zero projection of the
source store. The packet proofs yield exactly `Capture.packEnv` of that
projection, with no visible event and unchanged atomic state. This is an
agreement about the supplied tagged values. Static slot typing comes from
the profile. The execution theorems take the successful pure closure,
the source store and the shared primitives, and cover weak trees, finite
atomic returns and atomic infinite paths. Custom effectful producers use the
explicit packet contract above. [Pure endpoint](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Thms.lean)

The visible regression starts with a tick under pure capture and uses its
reply as the next tick operand. The atomic regression selects two distinct
inputs in reversed positional order and returns them in source order.
[Visible regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/ITree/Examples.lean) · [Atomic regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Examples.lean)

## Finite trace comparison

Two independently admitted and purely closed graphs can be compared at
matching typed interfaces. `InterfaceMatch` requires the same positional
capture types and the same type at the sole external exit. `MatchedInputs`
pairs the source stores and requires equal projected version-zero values at
each slot. The comparison shares the event family and tagged runtime values.
Each graph can use its own primitives, with the same implementation on its
source and packed sides. The interface witness relates static slots and
projected values. Any runtime typing invariant is a separate premise of a
client that needs it. [Interface](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Defs.lean)

`packed_pointwise_traceLE_iff` transports finite trace inclusion in both
directions over any family of matched inputs. Source observations run the
predecessor-indexed evaluator and use the same exit number and return tag
as the packed dispatcher. Requests and their typed replies pass through
unchanged. The proof uses the checked pure execution equality for each graph.
The result compares executions with supplied primitive interpretations.
[Transport](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Thms.lean)

The regression certifies, admits and closes two graphs independently.
Every seed gives inclusion from the partial tick graph to the total tick
graph. At seed `4`, replies `2` and `0` each pass through the self-edge's φ
operand to the next visit. Only the total graph requests `tick 0`, which
witnesses strict inclusion for the packed executions.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Examples.lean)

## Block-local simulation

`Local.Simulation` gives a sufficient rule for the trace comparison. Supply
a relation on pending transfers at aligned block boundaries and a relation
on the local body trees and their reply continuations. At a paired jump,
`Local.step_jump` exposes the actual predecessor lookup and parallel φ
assignment. It reads every operand in the outgoing store and passes the
updated store to the block body. This is where a client can establish its
live-register and runtime value invariants. Typed admission and matching
external profiles are required when transporting the result to packing.
[Local witness](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Defs.lean)

A local match must find the same indexed request and relate the continuations
for every reply, or find the same encoded exit. Paired internal transfers
return to the boundary relation. An unpaired left transfer must take an
actual step before consulting the relation again. Each match may follow
finitely many silent internal transfers on the right. The proof inducts
over the finite left normalization prefix and the finite trace, so even an
infinite silent loop needs no global termination premise. An observable
left prefix always requires a finite match on the right.
[Soundness](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Thms.lean)

The cyclic fixture checks separate admissions for renamed registers and
headers. The right entry passes through a silent block with its own typed
profile. At each header the selected operands must be the same numeric
value. A continuing reply writes it to the backedge operand on both sides.
The local proof yields inclusion for the actual pure packed dispatchers
at every seed.
[Fixture](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Certified/Pure/Trace/Local/Examples.lean)
