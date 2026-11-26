# Peggy paper coverage and reproduction

Silmaril has a typed PEG core, a repaired Figure 11 denotation, a structured
SIMPLE forward preservation proof, and several checked optimization and
reversion paths. The end-to-end replay below exercises the loop-free path.
The literal statement of Theorem 1 has a counterexample, and the general
reverter and historical Java experiments remain open.

The reference is Ross Tate, Michael Stepp, Zachary Tatlock and Sorin Lerner,
*Equality Saturation: A New Approach to Optimization*, LMCS 7(1:10), 2011,
arXiv:1012.1802v3, 80 PDF pages. SHA-256 of the PDF is
`5bb3630c9a2a4766c5614b19148e865ee0797c693607b2cdd700b27c38df0b94`.
Page links use PDF page numbers. PEG denotes **Program Expression Graph**.
[Paper](https://arxiv.org/pdf/1012.1802v3) · [Journal](https://lmcs.episciences.org/1016)

**Proved** refers to the stated Lean theorem under its listed hypotheses.
**Implemented** refers to executable code or fixtures with their stated
acceptance boundary. **Open** marks a missing or unsupported paper claim.
PR numbers identify canonical review artifacts, including work that may be
ahead of main. Module names below omit the common `Silmaril.SSA.` prefix.

## Graphs, forward translation and examples

| Paper locator | Coverage in Lean | Open or different |
| --- | --- | --- |
| §§1–3, worked optimizations | **Implemented and checked examples.** `tests/ssa/PEG.lean` exercises typed sharing, lazy branching and loop feedback. `tests/ssa/PEGSimple.lean` checks factorial and later sibling, branch-contained and nested loops. Selected rules and bounded optimization have independent fixtures. [Paper](https://arxiv.org/pdf/1012.1802v3#page=2) · [#3205](https://github.com/hiloopai/silmaril-lean/pull/3205) · [#3335](https://github.com/hiloopai/silmaril-lean/pull/3335) · [#3375](https://github.com/hiloopai/silmaril-lean/pull/3375) | The paper's full sequence of example optimizations, including inter-loop strength reduction and branch hoisting, has no complete replay. |
| §5.1, Fig. 11, Def. 5.1 and Thm. 1 | **Implemented** typed, numbered graphs in `PEG.Defs` and wiring checks in `RawGraph.check` in `PEG.Builder`. **Proved** structural and demand lemmas in `PEG.Thms` and `PEG.Semantics.Thms`, including `Graph.existsUnique_solves_of_wellFormed`, `Graph.demandWellFounded_of_check` and `Graph.observe_denote_mapOps`. [#3205](https://github.com/hiloopai/silmaril-lean/pull/3205) · [#3253](https://github.com/hiloopai/silmaril-lean/pull/3253) | Lean's structural guard strengthens the printed guard. See the discrepancy below. |
| §5.3, Def. 5.2 and Appendix A | **Proved** the largest syntactic invariance predicate and its semantic consequence in `PEG.Rules.Thms` (`invariantAt_largest`, `denote_invariant`), plus guarded rules including `phi_same_of_defined`, `theta_self`, `eval_invariant` and `pass_peel`. [#3358](https://github.com/hiloopai/silmaril-lean/pull/3358) | Open: the remaining discharge conditions and rules for the paper's partial-stream and language-specific examples. For example, `φ(c,a,a) = a` needs a defined condition for the Lean rule. Appendix A itself lists only rules relevant to Fig. 38, a subset of the historical engine's rules. |
| §6, Figs. 15 and 17, Thm. 2 | **Implemented** typed positional variables, primitive applications, fresh assignments, context projection, sequence, branches, while and one return. **Proved** `Program.translate_returns` in `PEG.Simple.Thms` (loop-free), `WhileProgram.translate_returns` in `PEG.Simple.While.Thms` (top-level while), and `translate_returns` in `PEG.Simple.Structured.Thms` (compositional loops). The structured compiler derives first exits and defined eval prefixes from finite source execution at fixed enclosing coordinates. It requires the supplied Boolean negation opcode to implement negation. `Structured.translate_wellFormed` proves the emitted graph itself meets Peggy's structural sentence admission. [#3306](https://github.com/hiloopai/silmaril-lean/pull/3306) · [#3335](https://github.com/hiloopai/silmaril-lean/pull/3335) · [#3375](https://github.com/hiloopai/silmaril-lean/pull/3375) · [#3427](https://github.com/hiloopai/silmaril-lean/pull/3427) | Successful source return implies the same defined PEG result (the structured theorem holds at every output index, including the paper's all-zero index). Failure and divergence are outside that implication. |

### Theorem 1 guard and observation

Definition 5.1(3) asks for a strictly enclosing θ **node** on each cycle
through an eval or pass. Take enclosing loop `o`, inner loop `l` and
`A = θ_o(E,0)`, `E = eval_l(B,1)`, `B = θ_l(0,A)`. The cycle uses A's
initial edge and B's feedback edge. The fixture checks all three printed
clauses and exhibits two solutions of the specialized Figure 11 equations
that disagree at index `(0,0)`. It also checks the cycle of actual demands.
`Graph.WellFormed` requires the strictly enclosing θ's **feedback edge**.
For this stronger guard the demand relation is well founded even with
arbitrary sample indices and all earlier eval-prefix indices. The unique
simultaneous solution uses lazy φ, θ's initial/previous feedback selection,
least eligible pass, and eval's defined-prefix check. The rank checker gives
a separate sufficient demand certificate. Relabelling preserves exact
observations, including bottom, under model reduct.
[Fig. 11 and Def. 5.1](https://arxiv.org/pdf/1012.1802v3#page=23) ·
[Thm. 1](https://arxiv.org/pdf/1012.1802v3#page=24) · [Fixture](../../tests/ssa/PEG.lean) · [Semantics](peg-semantics.md)

### Theorem 2 and completion

The paper already limits Theorem 2 to successful returns and explains the
discarded infinite-loop case. The Lean source `Exec` distinguishes finite
primitive failure from divergence (absence of a finite execution). A PEG
root has one bottom, and it can also be defined despite source failure in
an assignment outside the return's demanded dependencies. The loop-free
fixture checks the latter. Section 6's Figure 18 completion/effect-token
encoding has no delivered Lean preservation theorem here. The authors'
Coq `PEGSem.v` samples eval's selected index directly. Lean uses the
Figure 11 defined-prefix rule, so an undefined earlier sample can prevent
a defined later sample from being observed.
[Thm. 2 and Fig. 18](https://arxiv.org/pdf/1012.1802v3#page=36) ·
[Coq source](https://cseweb.ucsd.edu/groups/progsys/peg-coq-proof/PEGSem.v) ·
[Source semantics and comparison](peg-simple.md#comparison-with-the-authors-coq)

## Saturation, reversion and implementation

| Paper locator | Coverage in Lean | Open or different |
| --- | --- | --- |
| §4, Fig. 10 and (4.1)–(4.4); §5.2; §8.2 | **Implemented** sorted Egg explanation replay for ranked acyclic graphs and a guarded cyclic E-PEG certificate kernel. **Proved** `checkOutputs_figure11_sound` in `Peggy.Bridge.Figure11.Thms`, `observe_sound_of_rows` in `Peggy.EPEG.Selection.Thms`, and `saturate_least`, `saturate_perm`, `run_denote_sound` in `Peggy.EPEG.Saturation.Thms`. Saturation closes the partition on a fixed finite node table and supplied ground obligations. Semantic rule hypotheses or checked structural evidence justify the corresponding equalities. [#3256](https://github.com/hiloopai/silmaril-lean/pull/3256) · [#3284](https://github.com/hiloopai/silmaril-lean/pull/3284) · [#3313](https://github.com/hiloopai/silmaril-lean/pull/3313) | Open: (4.1)–(4.4) for general node-generating monotone analyses, and the correspondence of a Rete engine and its bounded worklist with that semantics. |
| §8.3, search and `SelectBest` | **Implemented** bounded single-root discovery and contextual ranked loop-free search. **Proved** `Candidate.sound` in `Peggy.Optimizer.Thms`, `optimize_min` and `compareOutputs_sound` in `Peggy.Optimizer.Contextual.Thms`. The contextual measure is the count of distinct reachable primitive and φ vertices, minimized among the explored, replay-checked candidates. `Result.sound` in `Peggy.Optimizer.Cyclic.Thms` covers elimination of a literal θ self-feedback row with a leaf initializer under a single-loop admission check excluding eval/pass. `SimpleValidation.Cyclic` reuses the checked replay with eval/pass demand ranks, then infers a single-loop SIMPLE schedule and proves defined-return agreement with the original PEG. `SimpleValidation.Cyclic.Source` compiles a top-level SIMPLE while and checks the redirected boundary, including eliminated invariant slots, to preserve successful source returns under target schedule totality and negation. [#3924](https://github.com/hiloopai/silmaril-lean/pull/3924) · [#3626](https://github.com/hiloopai/silmaril-lean/pull/3626) · [#3346](https://github.com/hiloopai/silmaril-lean/pull/3346) · [#3372](https://github.com/hiloopai/silmaril-lean/pull/3372) · [#3413](https://github.com/hiloopai/silmaril-lean/pull/3413) | Open: general cyclic discovery and extraction across eval/pass boundaries, and the paper's pseudo-Boolean costs, constraints, solver integration and optimality claim. |
| §7.1–7.5, Fig. 19 | **Implemented and proved** `PEG.Figure19` defines the row typing rules with separate printed and inward eval premises. Bounded checking yields a derivation for the designated roots. `Structured.translate_figure19` proves inward admission for every typed structured SIMPLE compilation. The compiler bridge checks an independent demand rank for Figure 11 observations. **Proved** `Certificate.revert_returns` and `Certificate.revert_run` in `PEG.Simple.Revert.Thms` for a checked, supplied single-output loop-free schedule. **Implemented** partial automatic ranking/scheduling in `PEG.Simple.Revert.Automatic`; `checkRanked_accepts_straightLine` proves acceptance for a narrower straight-line class. **Implemented** exact-recompilation extraction of a canonical seven-row scalar loop in `PEG.Simple.Revert.While`, with `Certificate.compile_eq` and source-return-to-observation `Certificate.observe_of_returns`. The ten-row pair extractor in `PEG.Simple.Revert.While.Pair` uses simultaneous updates from the old store. Its `Certificate.returns_of_defined` and the scalar counterpart recover source returns from defined PEG observations under guard and complete-step totality and the negation law. The pair fuel runner also has `Certificate.runFuel_of_defined`. **Implemented and proved** `PEG.Simple.Revert.While.Region.Automatic.extract` infers a typed boundary, demand rank and schedules for a restricted parentless single loop without compiler row numbering. `Certificate.returns_iff_observe` relates the emitted SIMPLE return to the original Figure 11 observation under guard and full-update totality and the negation law. `Certificate.exitWitness_of_defined` gives the finite first pass and the eval prefix. **Implemented and proved** `PEG.Simple.Revert.While.Nested.Automatic` infers a two-level form from the designated eval, parent table and scoped wires and validates it against the existing structured compiler table. Its `Accepted.returns_iff_observe` covers one scoped inner invocation per outer step. `Nested.Reindexed.Automatic` infers the form and both bijections, checks the full mapped table, and proves defined-return agreement at the input index. `Nested.Projected` composes that reverter with checked removal of rows outside the loop-bundle operand closure. [#3866](https://github.com/hiloopai/silmaril-lean/pull/3866) · [#3794](https://github.com/hiloopai/silmaril-lean/pull/3794) · [#3760](https://github.com/hiloopai/silmaril-lean/pull/3760) · [#3725](https://github.com/hiloopai/silmaril-lean/pull/3725) · [#3703](https://github.com/hiloopai/silmaril-lean/pull/3703) · [#3348](https://github.com/hiloopai/silmaril-lean/pull/3348) · [#3388](https://github.com/hiloopai/silmaril-lean/pull/3388) · [#3389](https://github.com/hiloopai/silmaril-lean/pull/3389) · [#3441](https://github.com/hiloopai/silmaril-lean/pull/3441) | Open: completeness of bounded Figure 19 recognition and general loop/branch extraction and sequencing. Structural `WellFormed` alone does not supply a reversion schedule. The graph-only single-loop checker requires one θ per initializer port and the eval/pass phase layout. |
| §7.6–7.9, optimized reversion | **Implemented** restricted sharing-aware placement with rejection in the loop-free scheduler, and simultaneous old-store updates with shared primitive bindings in the checked single-loop region. [#3388](https://github.com/hiloopai/silmaril-lean/pull/3388) · [#3441](https://github.com/hiloopai/silmaril-lean/pull/3441) | Open: simultaneous-copy scheduling across general control flow, loop and branch fusion, redundancy hoisting, MustEval and LICM. |
| §8.1 and Appendix A, Java | **Implemented and proved** resolved integer-field loads/stores in `Peggy.FieldHeap.Thms`, including guarded forwarding and disjoint-field laws. Observations include exact heap, sticky first fault and optional read values; a completed faulting read (`some none`) differs from PEG bottom (`none`). `run_eq_observe` in `Peggy.FieldHeap.Linearize.Thms` proves exact ordered observation for an accepted straight-line single-token chain. [#3391](https://github.com/hiloopai/silmaril-lean/pull/3391) · [#3421](https://github.com/hiloopai/silmaril-lean/pull/3421) | Open: Java bytecode conversion, full object/array/allocation/call and exception semantics, and general heap linearization. The linearizer rejects token forks. |
| §8.4, separate eval and pass | **Implemented and proved** the split in `PEG.Semantics.Thms`. The structured frontend shares one pass across the evals of the carried values for each loop. [Paper](https://arxiv.org/pdf/1012.1802v3#page=65) · [#3253](https://github.com/hiloopai/silmaril-lean/pull/3253) · [#3375](https://github.com/hiloopai/silmaril-lean/pull/3375) | The split is part of the denotation. General optimization and reversion across these nodes remain open. |
| §9 and Fig. 38, empirical evaluation | **Reproducible fixture** for one typed SIMPLE pipeline below. | **Historical measurements:** the timings and space results, 84% complete saturation, and validation of 98% of 3,416 Soot-optimized methods with three reported miscompilations require the original Java toolchain, rules, workloads and experiment configuration. No Lean reproduction of those measurements is delivered here. [§9](https://arxiv.org/pdf/1012.1802v3#page=65) · [§9.3](https://arxiv.org/pdf/1012.1802v3#page=69) |

The graph-only checker starts at the designated eval and reads the sampled
θ, the shared pass and its unary Boolean exit operation. It orders carried
values by the typed parameter ports that initialize them. Each port must
initialize exactly one θ and the table must contain exactly that many θs.
Duplicate or missing θ initializers are rejected, even on unused rows.
The existing supplied-boundary checker remains available.

The inferred rank separates eval, pass and interior rows by label,
compares the iteration counter next, then synthesizes heights on the
remaining same-phase, same-index edges by removing sinks. The existing
demand checker validates all graph rows. Each φ-free slice starts with the
old θ vector, emits each primitive row once, and rejects reads of a pass,
eval or undeclared θ. `Automatic.extract_accepts` proves recognition
relative to a schedulable region boundary with unique θ initializers and
a bounded rank in this phase layout.
The update slice commits the entire typed vector at once. SIMPLE caches
the guard in a loop-local slot to keep multi-row guards executable with
the existing while syntax. The correspondence concerns defined returns.
A partial update whose result the PEG never demands can prevent a SIMPLE
return, so the reverse direction requires totality of the complete update.
[`Automatic.Defs`](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Automatic/Defs.lean) ·
[`Automatic.Thms`](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Automatic/Thms.lean) ·
[Regression fixture](../../tests/ssa/PEGCanonicalWhile.lean)

The two-level reversion form uses a typed capture projection on the old
outer vector, one child while with a loop-free body, and a loop-free commit
from the child's full final store to the next outer vector. The child and
commit can access only their local contexts. An old value needed at commit
is carried through an explicit capture slot. The checker compares the
numbered table and loop parents with the existing structured lowering of
this form, including the capture, feedback, and exit wires.

The automatic entry point follows the designated eval to the outer pass
and selects the unique direct child pass. The shared eval bundle of
each loop identifies its ordered θ slots. Child initializers must read
the outer θ vector and may repeat a capture. The child update reads only
the child θ vector and local primitive assignments. The commit reads
only the child eval bundle and its own primitive assignments. Each guard
is a carried Boolean or a single primitive over its carried values. Both
loops use the same unary Boolean negation opcode. The probe follows
dependency edges and reuses the checked primitive scheduler. It orders
bundles and assignments by the structured compiler's row order, then
passes the inferred form to the exact-table checker. Primitive assignments
must be reachable from feedback or commit roots in their respective
slices. The original graph-only API supports the numbered compiler layout
with the loop-ID space indexed by rows. The supplied-mapping entry point accepts a
numbering from compiler positions to input rows and loop keys, then runs
the automatic checker on the reindexed input. The finite checker verifies
both inverse laws for each proposed bijection. A graph-level table
comparison can check a proposed isomorphism against a fixed reference
graph. It compares the mapped sorts, labels, ordered operands, roots and
loop parents.

`Structured.translate_while_trace_of_defined` recovers a finite outer trace
from a defined eval using the first pass and the selected sample prefix.
Every continuing outer store must have a successful complete body step.
For the checked two-level form, this requires the guard to be total, the
child to terminate successfully on continuing captures, and the commit
to succeed on completed child stores. The Boolean negation law relates
the exit flag to the continuation test. Successful SIMPLE returns imply defined PEG observations by the existing
structured compiler theorem. The executable fixture recovers two valid
capture layouts and rejects a child initializer that reads outside the
outer θ vector and a missing child parent.
[`Nested.Automatic.Defs`](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Automatic/Defs.lean) ·
[`Nested.Automatic.Thms`](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Automatic/Thms.lean) ·
[Regression fixture](../../tests/ssa/PEGCanonicalWhile.lean)

The graph-level reindexing proof transports the loop-index vector,
evaluation demands and rank certificates. The reindexed Figure 11
solution agrees on all requests and ordered roots, including bottom.
The graph-only reverter uses that equality to state defined-return
agreement at the input graph's original index. It infers the same
two-level form with outer slots in parameter order, child slots in
input eval order, and primitive assignments in scoped dependency order.
It compiles that form to obtain a reference graph.

The mapping worklist starts with the designated roots and every eval in
both bundles, including slots omitted from the return. It follows
ordered operands, loop labels and parent links. Each endpoint can be
paired only once, and revisiting a consistent pair leaves the worklist
unchanged apart from consuming that entry. Every row of both graphs
must be covered by these seeds. Unpaired loop keys must be parentless
and are paired in ascending order. The finite equivalence checker validates
both bijections, and the reference-table checker compares the full table.
Admission covers the supported two-level compiler image up to checked isomorphism, with
coverage by the selected anchors required. The regression independently
permutes row and loop IDs, returns 10 via the graph-only API, and rejects a
well-sorted child capture that escapes the outer θ scope.
[Graph checker](../../Silmaril/SSA/PEG/Reindex/Defs.lean) ·
[Mapping inference](../../Silmaril/SSA/PEG/Reindex/Automatic/Defs.lean) ·
[Figure 11 transport](../../Silmaril/SSA/PEG/Semantics/Reindex/Thms.lean) ·
[Graph-only two-level reverter](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Reindexed/Automatic/Thms.lean)

The checked projection admits a larger input whose extra rows are
outside the operand closure of the designated return and every eval
in the outer and child bundles. The worklist follows every ordered
operand occurrence, including both θ inputs, both φ arms, and eval's
pass operand. The checker verifies that selected rows are distinct and
that every retained operand and root maps back to its exact typed
reference. All loop keys and parents stay in the table. The proof
restricts scope and checked demand ranks, preserves every demand of a
retained request at its original index, and transports the Figure 11
root tuple including bottom.

The projected two-level extractor builds this closure from the input
graph and runs the graph-only reverter on the compacted table. The
compacted table must still pass the full isomorphism check, including
the unchanged loop metadata. Comparing with the full graph's global
denotation additionally requires well-founded demands on the full
graph. The fixture adds a dead primitive consumer to a renumbered
two-level graph and returns 10 after projection. The unequal row and
loop-key counts rule out isomorphism to any structured compiler image.
An explicit selection
that retains a child θ but drops its capture is rejected.
[Projection and transport](../../Silmaril/SSA/PEG/Projection/Thms.lean) ·
[Projected two-level reverter](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Projected/Thms.lean) ·
[Regression fixture](../../tests/ssa/PEGCanonicalWhile.lean)

### Figure 19 typing and the semantic gate

`PEG.Figure19.Derives` represents the judgment on a typed row at a
numeric depth with an assumption list. The return sort comes from the
row. The graph fixes the typed input ports corresponding to Γ, and
its ordered roots stand for the context's output bindings.

| Paper clause | Lean correspondence |
| --- | --- |
| Type-PEG-Context | `CFGContext` requires the judgment for every ordered designated root. |
| Type-PEG | Each root starts at depth zero with an empty assumption list. |
| Type-Param | A `param` label carries its typed port of Γ. |
| Type-Op | The opcode carries its ordered profile. `Derives.op` requires a derivation for each operand at the current depth and assumptions. |
| Type-Phi | The flag is Boolean and both alternatives have the result sort. Each of the three operands is checked in the same context. |
| Type-Theta | The initial operand is checked one depth above the θ in the nesting tree. The feedback operand is checked at the θ depth with the exact row and depth added to the assumptions. |
| Type-Eval-Pass | Eval's index argument must name a pass with the same loop key. Both the sampled value and the pass predicate are typed at the sampled depth. Every retained assumption must be strictly shallower. |
| Type-Reduce | The conclusion can raise the allowed depth and extend the assumption list. The premise can therefore lower the bound and discard assumptions. |
| Type-Assume | A previously assumed θ row may close a derivation at its declared depth. Row identity and sort are retained. |

The printed eval premise has `surrounding = sampled + 1`.
`EvalDirection.printed` keeps that premise, and
`CFGContext.printed_no_root_eval` proves that it rules out a directly
designated eval even with Type-Reduce. The structured compiler bridge
uses `EvalDirection.inward`, with `sampled = surrounding + 1`, to
observe an immediate child from its parent. Checking the same loop key
refines the paper's depth-only spelling for numbered sibling loops.
The executable checker also validates the depth assignment against the
loop parent table.

The checker is a bounded search that returns derivation evidence.
It tries a θ assumption before expanding feedback and uses one specific
Type-Reduce choice at eval, retaining the assumptions strictly above
the sampled loop. Only dependencies needed for the designated roots
are typed. Search completeness and a fuel bound that guarantees
checker acceptance for compiler output remain open.

`Structured.translate_figure19` proves inward admission for every
typed program supported by the structured SIMPLE compiler, including
branches and arbitrarily nested whiles. The theorem uses the checker's
inferred depth assignment. Each parent key precedes its child in the
compiled table, so a table-length traversal computes the exact depths
and satisfies `FitsForest`.

The proof tracks the compiler's embedded rows and typed store ports
through sequencing. A branch derives both arms and the shared φ
operands at the enclosing depth. For a loop, initializers inherit
derivations at the enclosing depth. The feedback derivation introduces
one θ hypothesis at a time and decreases the number of unassumed
carried rows, covering mutually recursive slots. The resulting θ and
guard derivations justify each eval with the pass emitted for the
same loop key. Regression cases include a nested branching update
with two mutually dependent carried values.
[Structured compiler admission theorem](../../Silmaril/SSA/PEG/Simple/Structured/Figure19/Thms.lean)

`checkGuarded` separately validates a rank against the entire graph,
ordering all Figure 11 demands, including every index that pass and
eval may sample. First exit existence and prefix definedness remain
properties of the denotation. Implications from the typing judgment to
that demand guard or to Definition 5.1 remain open. The regression derives
admission for a compiled outer while whose inner while updates
through a φ, and the compiler bridge supplies its successful-return
observation using the checked rank. A same-depth, wrong-key pass
retains a valid demand rank and violates the typing judgment.
General lexical scope consequences, extraction and its scheduling
proof remain open.
[Figure 19](https://arxiv.org/pdf/1012.1802v3#page=41) ·
[Typing and checker](../../Silmaril/SSA/PEG/Figure19/Defs.lean) ·
[Structured compiler bridge](../../Silmaril/SSA/PEG/Figure19/Structured/Thms.lean) ·
[Regressions](../../tests/ssa/PEG.lean)

### Checked placement of a shared branch inside a loop

`Region.Placement.extract` takes a one-loop PEG and two row IDs, a
feedback-root φ and a proposed shared primitive. It discovers the carried
vector from the designated eval and checks the original same-key pass,
parameter initializers and return slot. It derives the placement
context from the forest depth and the installed θ rows. The checker
validates the inward root derivation and checks the φ at the loop depth
under exactly those θ assumptions. The strict path transports that
derivation from an arm to the shared row.

`StrictPath.depth_le` proves that a strict dependency on one of those
θ rows forces the shared primitive to be typed at that loop's depth or
deeper, even with Type-Reduce. The derivation at the loop depth supplies
the matching upper bound on the minimum depth.
`StrictPath.defined_of_phi` independently proves that a defined φ
implies definedness of a common strict dependency at the same index.
The path checker follows ordered primitive operands and stops at control
or recurrence nodes. Each arm needs its own path to the proposed shared
row. This suffices even with pure partial primitives.

| Paper section | Checked placement boundary |
| --- | --- |
| §7.3 | One parentless loop, one parameter initializer per θ slot, an eval of one current carried value, and the same loop key on the pass. Update slices read θ slots as the old store. The guard and exit boundary reuse the single-loop certificate. |
| §7.4 | One φ directly in the feedback vector becomes one SIMPLE branch. Its guard and shared primitive are scheduled over the old store before the branch. Each arm has its own primitive schedule and returns its result plus the inherited store. Extra φ, eval, pass, or unbound θ dependencies in the scheduled slices cause rejection. |
| §7.5 | Primitive bindings use ordered, already available operands and fresh temporaries. The join binds the φ once, and the final projection commits the whole update vector simultaneously. |
| §7.6–7.7 | Loop and branch fusion remain open. |
| §7.8 | The original checker uses one strict path from each arm. The nested-branch extension below computes demand sets and discovers a shared row. General MustEval and the paper's progress and precision requirements for all PEG contexts remain open. |
| §7.9 | The shared row stays in the continuing update, after the while guard. LICM, EvalCond and loop peeling remain open. |

`Accepted.returns_iff_observe` relates the emitted SIMPLE return to the
original graph. It uses a validated whole-graph demand rank,
the existing finite first-pass and eval-prefix construction, the
negation opcode law, and successful evaluation of the guard and full
lazy update on every defined old store. The sharing theorem itself does
not require this store-totality premise. The new fixture is a manually
wired, live feedback φ with a shared decrement, outside #3893's
projected two-loop layout and rejected by the former primitive-only
single-loop scheduler. It returns zero from five in three steps.
Proposing the partial true-arm instruction for the same placement is
rejected even though the graph has an inward derivation and the false
arm can return successfully. General Figure 19 extraction and nested
placement remain open.
[Placement checker and theorem](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Placement/Thms.lean) ·
[Regression](../../tests/ssa/PEGCanonicalWhile.lean) ·
[Paper §§7.3–7.9](https://arxiv.org/pdf/1012.1802v3#page=43)

### Same-index MustEval for nested lazy branches

`Figure19.MustEval.analyze` computes a table of finite sets for a typed
PEG. In the expression slice, each row adds itself. A primitive unions
all operand sets. A φ unions its flag set with the intersection of the
two arm sets. Parameters and the θ, eval and pass boundaries are leaves.
One round reads the previous table, so shared children do not trigger
repeated recursive searches. From singleton sets, the implementation
runs one round per graph row. `MustEval.stable` proves that a row is
stable once the bound exceeds its rank in the followed operand DAG.

`MustEval.defined` proves that membership at a defined root forces the
member to be defined at the same input and iteration in any Figure 11
solution. The proof uses strict primitive operands and the actual lazy
φ rule, with partial instructions allowed. The local rank controls the
round bound. The independent whole-graph demand rank justifies the
Figure 11 solution.

`Region.Placement.MustEval.extract` takes the graph alone. It checks the
inward admission and single-loop boundary, then tries feedback-root φ
rows and shared primitives demanded by both arms. It excludes candidates
already demanded by the flag and requires a strict dependency on an old
θ slot. The scheduler binds the selected primitive once before the outer
branch in each continuing update. Nested φ are supported at arm roots,
with primitive guard and leaf slices. Branch-local bindings stay in their
arms and the final projection commits the full old-store update
simultaneously. Other φ dependencies, including a φ used as an operand
of a primitive slice, can cause rejection.

The placement theorem uses only definedness of the original branch on
the current old state. The emitted-loop successful-to-defined theorem
uses the checked rank and negation law. The reverse direction still
uses guard and complete lazy-update totality because the designated
PEG observation can discard other slots. The regression discovers a
partial primitive behind two nested φ arms, which the strict-path
test in #4059 rejects. An arm-specific partial row reachable through
both nested branches is rejected as a candidate, and a continuing
execution that skips it succeeds. A zero-trip execution skips the
update entirely.

Section 7.8 starts on p. 53 and gives Definition 7 on p. 55. The transfer
implements its root, strict-op and φ-condition propagation for this
expression fragment after stabilization, with the additional
both-arms test for sharing. Statement nodes, arbitrary contexts,
semantic guard implications and general reversion progress are outside
this analysis. Section 7.9 starts on p. 56 and introduces EvalCond on
p. 57. The implementation places work inside a continuing iteration
only. It covers neither EvalCond implications nor motion across loop
boundaries, zero-trip hoisting, or loop peeling.
[§7.8](https://arxiv.org/pdf/1012.1802v3#page=53) ·
[Definition 7](https://arxiv.org/pdf/1012.1802v3#page=55) ·
[§7.9](https://arxiv.org/pdf/1012.1802v3#page=56) ·
[EvalCond](https://arxiv.org/pdf/1012.1802v3#page=57) ·
[Analysis theorems](../../Silmaril/SSA/PEG/Figure19/Placement/MustEval/Thms.lean) ·
[Placement](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Placement/MustEval/Thms.lean)

### Guarded hoisting of a parameter-fed invariant

`Region.Hoist.check` accepts a parentless one-loop PEG, a typed region
descriptor and one proposed invariant primitive. The existing boundary
checker validates the parameter initializers, θ feedback, invariant
parameter slots, same-loop pass and designated eval. The whole-graph
demand rank is inferred and checked independently. Primitive guard and
remainder orders are synthesized over their available typed scopes.

The proposed binding can read only parameter rows already available in
the old store. It must occur in the computed same-index must-demand set
of a complete update root and be absent from the guard schedule.
`Site.invariantAt` derives the paper's Definition 5.2 for that row.
`Site.cache_of_defined` combines §7.8 must-demand soundness at a defined
update root with soundness of the invariant predicate, yielding one
defined value at every index of the parentless loop. The interpretation
may supply partial primitives.

The reference SIMPLE update binds the primitive as its first assignment.
The emitted SIMPLE first computes the same entry guard. Its true arm
initializes the cache once, then enters a while whose update reads the
cache, commits the old-store update simultaneously, and recomputes the
guard on the new store. Its false arm projects the old store directly.
The cached slot is immutable across the loop and absent from the return
interface. The regression runs four continuing iterations with a
two-unit decrement. At zero iterations the same primitive is undefined
on the input, yet the program returns zero without evaluating it. A
proposed binding that reads the changing θ is rejected.

`Accepted.trace_placement` starts with a successful entry guard and
a finite reference trace with defined true continuation tests, successful
full updates at their actual old stores, and a defined false exit test.
The first executed update supplies the defined root that justifies the
initial cache. Replaying each step compares the scheduled operand reads
at the same state and uses invariance to reuse the cached value. The
negation law yields the exact first pass and all carried eval prefixes
in the original graph. `Accepted.preserves` gives the corresponding
successful-return implication. This path needs no global guard, update,
or hoisted-op totality. A defined scalar PEG observation by itself can
discard failing updates, so the preservation theorem uses the finite
reference trace. General EvalCond, loop peeling, arbitrary invariants
and nested code motion remain open. No claim about fault equality.

[Placement and trace theorems](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Hoist/Thms.lean) ·
[Regression](../../tests/ssa/PEGStructuredTheta.lean) ·
[§7.9 and Figure 33](https://arxiv.org/pdf/1012.1802v3#page=56) ·
[Figure 34 and EvalCond](https://arxiv.org/pdf/1012.1802v3#page=57)

### Selection cycle legality

`EPEG.Selection.PrintedCycles` models the three reachability clauses
on p. 64 of §8.3 for the wired candidate. A chosen non-θ reaches each
child. Reaching a chosen non-θ extends reachability to its children.
For each non-θ, the diagonal reachability variable is false.
`PrintedCycles.excludes_nonTheta_cycle` proves that these clauses
exclude a nonempty cycle of chosen non-θ rows. Root and class constraints
from p. 63 are separate.

In the counterexample, the source θ feeds itself through its second
operand and initializes from a distinct parameter. The existing
self-feedback rule soundly merges their classes. Selecting the θ as the
representative also for the first operand gives a one-row table with both
operands pointing to θ. The ordered class wiring check succeeds. All
rows are selected, and setting every reachability variable false satisfies
the three printed clauses. The first operand yields an initial-edge
self-cycle, violating Definition 5.1(1) regardless of the second operand.

`FeedbackRank.infer` synthesizes and checks a decreasing rank on all
materialized edges except θ feedback edges. In particular, the checker
visits initializer and observer operands as well as strict operands.
`FeedbackRank.feedbackCycles` proves Definition 5.1(1) for this table.
The bounded cyclic extractor uses the same certificate for its structural
admission and retains it in the replay gate alongside the independent
ordered class, root and native demand checks. It rejects the
self-initializer, and the executable positive regression retains a live
θ → primitive → θ recurrence through a feedback edge. Loop forest and
scope, cycles through observers, Figure 19 admission, and semantic
equality require separate evidence. This covers the displayed cycle
defect and its repair for materialized selections. The pseudo-Boolean
objective and general SelectBest search and optimality remain open.
[Definition 5.1](https://arxiv.org/pdf/1012.1802v3#page=23) ·
[§8.3 class constraints](https://arxiv.org/pdf/1012.1802v3#page=63) ·
[§8.3 cycle constraints](https://arxiv.org/pdf/1012.1802v3#page=64) ·
[Selection legality](../../Silmaril/SSA/Peggy/EPEG/Selection/Legality/Thms.lean) ·
[Regression](../../tests/ssa/PeggyEgg.lean)

## Dialects, institutions and IR bridges

These are Silmaril extensions to the paper. The direction of each arrow
below is the sentence or program translation direction. Comorphism
models are pulled back in the opposite direction.

| Interface | Proved scope |
| --- | --- |
| `Peggy.Dialect.sentenceFunctor`, `Peggy.Institution.inst`, `Peggy.Dialect.Equation.holds_map` | The signature category fixes the sorts and maps opcodes forward, preserving ordered operand/result profiles. The sentence functor relabels equations of structurally admitted PEGs. The contravariant model functor takes reducts of discrete partial interpretations. Satisfaction is equality of ordered optional values for every defined input tuple and every index. `Peggy.Institution.Family.Defs` supplies `familyComorphism` and `familyChange` for functorial dialect families. [#3229](https://github.com/hiloopai/silmaril-lean/pull/3229) · [#3380](https://github.com/hiloopai/silmaril-lean/pull/3380) |
| Many-sorted equational logic → total-primitive Peggy | `Peggy.Bridge.Equational.Thms`: `comorphism`, `exact_satisfaction`, `modelExpansive`, `entails_compile_iff`. Term compilation and model expansion give entailment equivalence for the stated total-primitive subinstitution. [#3414](https://github.com/hiloopai/silmaril-lean/pull/3414) |
| Ordered value PEG → regionless RVSDG → regionless MLIR | `observe_translate` in `PEG.Bridge.RVSDG.Thms` and `observe_translateMLIR` in `PEG.Bridge.MLIR.Thms` cover ordered zero-loop pure PEGs with total primitives and the induced models. `Peggy.Bridge.IR.Thms` bundles `peggyToRVSDG`, `rvsdgToMLIR`, `peggyToMLIR` and `peggyToMLIR_modelExpansive` for the restricted institutions. [#3291](https://github.com/hiloopai/silmaril-lean/pull/3291) · [#3376](https://github.com/hiloopai/silmaril-lean/pull/3376) |
| Canonical PEG loop → structured RVSDG θ | `returns_iff_observe` in `PEG.Bridge.Theta.Thms` relates the RVSDG return to the PEG first-exit observation for the canonical total two-carried-slot, single-loop form. [#3344](https://github.com/hiloopai/silmaril-lean/pull/3344) |
| Ordered value PEG → RVSDG → typed λRTL/forward CFG; scoped PEG diamond → λSSA | `observeCFG_peg` in `PEG.Bridge.ForwardCFG.Thms` covers the ordered zero-loop total value path. `ScopedDiamond.lower_eval_iff` in `PEG.Bridge.LambdaSSA.Thms` covers the scoped zero-loop diamond. General looping/effectful SSA, CFG or MLIR and machine RTL/Wasm bridges are open. [#3316](https://github.com/hiloopai/silmaril-lean/pull/3316) · [#3404](https://github.com/hiloopai/silmaril-lean/pull/3404) |

## Replay the end-to-end SIMPLE demo

Use a checkout of Silmaril with Git, Make, Python, Node.js and elan available. Fetch
the canonical PR ref, then create a detached worktree at the audited demo
commit. The checkout's `lean-toolchain` selects
`leanprover/lean4:nightly-2026-11-05` and its Lake manifest pins the dependencies.
[PR #3403](https://github.com/hiloopai/silmaril-lean/pull/3403) ·
[Demo contract and sources at the audited revision](https://github.com/hiloopai/silmaril-lean/blob/3fbdc9225cc9fa4ff6f507e1f4aee124127a2f9f/docs/projects/peggy-simple-validation.md)

```sh
git fetch origin refs/pull/3403/head
git worktree add --detach ../silmaril-peggy-demo 3fbdc9225cc9fa4ff6f507e1f4aee124127a2f9f
cd ../silmaril-peggy-demo
elan toolchain install "$(cat lean-toolchain)"
make check CHECK_TARGETS='+Silmaril.SSA.Peggy.SimpleValidation.Thms PEGCoreTests PeggyEggTests PeggySimpleValidationTests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggySimpleValidation.lean
lake env leanchecker Silmaril.Proofs.SSA.Peggy.SimpleValidation.Correctness
lake env leanchecker Silmaril.SSA.Peggy.SimpleValidation.Thms
lake env leanchecker tests.ssa.PeggySimpleValidation
```

`Peggy.SimpleValidation.optimize` compiles typed loop-free single-result
SIMPLE, discovers and replays bounded contextual rewrites, selects a
candidate, and synthesizes and checks its reversion schedule.
`Peggy.SimpleValidation.Thms` exposes `Accepted.returns`,
`Accepted.runLoopFree` and `optimize_preserves_returns`. Given an accepted
result, rule laws and a successful source execution, the emitted SIMPLE
program returns the same value. Replay preserves exact ordered PEG
observations, including undefinedness. The entire pipeline has the narrower
successful-return contract and can reject a selected candidate during
reversion without searching for a fallback.

The standalone fixture uses `#guard_msgs` to check the results silently.
At input `(true, 14)`, depth zero leaves the reachable application count
at 5 and emits `add, add, add, bad`. Depth one lowers it to 4 and emits
`triple, add, bad`. Both return `some 84`. The false arm returns `none`
at depth one. A separate input program whose sharing would cause duplicate
writers is rejected with `Rejection.reversion`.
[Executable fixture](https://github.com/hiloopai/silmaril-lean/blob/3fbdc9225cc9fa4ff6f507e1f4aee124127a2f9f/tests/ssa/PeggySimpleValidation.lean)

## Remaining work in priority order

1. **Close the cyclic path from structured frontend through reversion.**
   Relate the Figure 19 typing rules to the repaired guard. Extend checked
   placement from one hoist across nested branches in a parentless loop to
   multiple update roots and nested loop regions. Carry first-exit and prefix obligations through selection
   and reversion. General extraction, fusion, MustEval and LICM remain open beyond the checked fragments.
2. **Formalize the general saturation and cost interfaces.** Model
   node-generating analyses and prove (4.1)–(4.4) with their hypotheses.
   Relate worklist execution and constrained selection to that model. Port
   Appendix A rule families with their definedness and language hypotheses,
   then replay the optimization examples of §§2–3 and Fig. 38. Keep the
   literal Theorem 1 counterexample and the repaired theorem side by side.
3. **Prove a separate completion-sensitive refinement.** Start with the
   discarded-failure and discarded-loop examples. Specify which returned
   values, faults and termination facts the token or trace observes before
   extending the compiler and rewrite checker. Theorem 2's existing
   successful-return implication remains the paper claim.
4. **Extend the Java and experimental coverage.** Model bytecode and the
   heap/exception behaviors needed by the historical frontend and
   linearizer, then verify the relevant translation-validation path.
   Separately pin the historical workloads, engine/solver and Soot versions,
   and rerun the §9 measurements. Full IR comorphisms for loops/effects are
   a distinct extension, with additional model and observation obligations.
