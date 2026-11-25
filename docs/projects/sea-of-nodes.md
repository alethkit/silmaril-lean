# Sea of Nodes source-to-Lean coverage

C1 inventories the original Sea of Nodes design, its algorithms, and the
official Simple tutorial. The [proof sequence](#proof-sequence) scopes the
incremental Lean work for C2. The local coverage claims below refer to
Silmaril at `f32f986f8780a179d01365ace2e92dfc01c0b8e9`. Every Sea of Nodes
obligation in the source tables is open. The [existing Lean results](#existing-lean-results)
give specific interfaces, proof patterns, and observation models to build on.

## Editions and source boundaries

| Work | Edition and full text used | SHA-256 of PDF |
| --- | --- | --- |
| Clifford Noel Click, Jr., *Combining Analyses, Combining Optimizations* | Rice University PhD dissertation, February 1995 on the title page, handle `1911/16807`. The deposit is a 151-page scan. Section references below use printed numbering. Appendix A begins on printed p. 119, PDF p. 130. [Rice record][thesis] · [Rice scan][thesis-pdf] | `30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c` |
| Cliff Click, *From Quads to Graphs: An Intermediate Representation’s Journey* | Rice University Center for Research on Parallel Computation, `CRPC-TR93366-S`, October 1993. The 29-page report includes the manuscript dated October 18, 1993. The live Rice link returned 404. [Archived Rice PDF, 2025-03-30][quads] | `8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b` |
| Cliff Click and Michael Paleczny, *A Simple Graph-Based Intermediate Representation* | ACM SIGPLAN Workshop on Intermediate Representations (IR ’95), pp. 35–49, also *SIGPLAN Notices* 30(3). Both ACM records identify the same paper. [Proceedings][ir] · [Notices][ir-notices] · [Oracle PDF][ir-pdf] | `9c12e5cd0ee54beb51436b25aec73c45855bb0eb5bafaa76ee4135edeadca17c` |
| Cliff Click, *Global Code Motion/Global Value Numbering* | PLDI ’95, pp. 246–257, also *SIGPLAN Notices* 30(6). The slash is ACM’s catalog punctuation. The linked UW course now serves an identity-provider page. [Proceedings][gcm] · [Notices][gcm-notices] · [Archived UW PDF, 2014-09-08][gcm-pdf] | `9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23` |
| Cliff Click and Keith D. Cooper, *Combining Analyses, Combining Optimizations* | ACM’s catalog title for the article in *TOPLAS* 17(2), March 1995, pp. 181–196. This is the coauthored article linked from Simple chapter 1. Use it alongside thesis chapter 3. [ACM][combining] · [Archived ACM PDF, 2025-09-16][combining-pdf] | `579ee1cc4e73d97b7741e0a8f4eceed0af8a6aee65d162b7114ad652abdc1a32` |
| Michael Paleczny, Christopher Vick and Cliff Click, *The Java HotSpot™ Server Compiler* | USENIX JVM ’01, April 2001. Its compiler overview cites the workshop paper and its GCM section cites Click’s scheduler. It supplies a historical industrial comparison. [USENIX proceedings PDF][hotspot] | `ad5091a200cf32752e2dc4150b506934ff7d460b4fe49076acd128e39219586e` |
| Matthias Braun et al., *Simple and Efficient Construction of Static Single Assignment Form* | CC 2013, LNCS 7791, pp. 102–122. Its SSA construction and related-work sections connect direct construction to Click–Paleczny and HotSpot. [Springer][braun] · [Authors’ PDF][braun-pdf] | `01f0b6d558096c27c1f37f4b451b8c4932dc200cee4e86d07357f0dacf21aa6a` |

The [organization reading list][org] points to the Rice dissertation and
calls out Appendix A. [Simple chapter 1][s01] adds the TOPLAS article and
two decks by Click. *How To SSA C2-Style* (`EasySSA.pdf`) illustrates
construction and explicitly drops minimality as a goal. *Sea of Nodes*
(`SeaOfNodes.pdf`) illustrates graph semantics, optimization and scheduling.
Use these as worked examples under the corresponding papers and Simple
chapters. The [REBASE 2026 deck and notes][rebase] give a newer walkthrough,
including the memory and SCCP examples. The SHA-256 values are
`e666c44f546c9ef563d0fba6c9d5b0fbbac73a394a793f01cfc34ed2f7a18be6`
for *How To SSA* and
`ab41d9a977843a13ca6e7cc71ae4b1516b4a8a160427425769ec3f28b66c175b`
for *Sea of Nodes*. [How To SSA PDF][easy] · [Sea of Nodes PDF][slides]

The report’s bibliography and the later papers identify two predecessor
algorithms relevant to the proof sequence. Cytron et al.’s *Efficiently
Computing Static Single Assignment Form and the Control Dependence Graph*
(TOPLAS 13(4), 1991) gives the dominance-frontier baseline. Wegman and
Zadeck’s *Constant Propagation with Conditional Branches* (TOPLAS 13(2), 1991)
gives the executable-edge and sparse-propagation baseline. Alpern, Wegman
and Zadeck’s *Detecting Equality of Variables in Programs* (POPL 1988) gives
the congruence-partition baseline for the thesis’s stronger algorithm.
Treat these as algorithm references for the relevant slice. Full-text
section coverage for these predecessor papers is outside this inventory.
[Cytron et al.][cytron] · [Wegman–Zadeck][wegman] · [Alpern et al.][alpern]

Use Braun et al. §§2.2–2.3 for demand-driven SSA and incomplete blocks.
Its §§3–4 separate redundant-Phi elimination and the assumptions for
minimality. Prove construction preserves behavior first. An extension
claiming pruned or minimal SSA needs the corresponding properties for
its own CFG class. [CC 2013 paper][braun-pdf]

Webb, Hayes and Utting’s *A Formal Semantics of the GraalVM Intermediate
Representation* (2021) and *Verifying Term Graph Optimizations using
Isabelle/HOL* (2023) give comparison points for executable graph semantics
and verified graph rewrites. Their venue records establish the scope of the
comparison. Matching Graal’s node semantics or transferring its Isabelle
proofs would require a separate correspondence. [Graal semantics][graal] ·
[Term graph optimizations][termgraphs]

## Original design and algorithms

The technical rows name the proof target independently of the implementation
in any one edition. Repeated concepts share one target. Preserve meaningful
differences, including where scheduling is allowed to speculate and which
analyses account for loop feedback.

### From Quads to Graphs

| Report sections | Open Lean obligation |
| --- | --- |
| §§1–2, introduction, quads and use-def information | Give ordered three-address execution a reference meaning. Show use-def lookup agrees with reaching values where defined. State the conservative assumptions of one-pass optimization at unresolved edges. |
| §3, static single assignment | Track the current definition of each variable and construct predecessor-indexed join inputs. Show that SSA construction preserves the quad execution, including a loop where a provisional backedge definition is later resolved. |
| §4, control-flow dependence | Make a definition’s execution condition explicit. Show that removing a redundant φ or contracting a control path preserves predecessor identity and the selected values. |
| §5, engineering concerns | State the invariants of replacement, inverse-use maintenance and deletion. Treat allocation strategy and object dispatch as implementation choices unless an implementation refinement exposes them. |
| §6, two tiers to one | Encode the CFG as control nodes, Regions and Ifs. Prove agreement with block execution, including the shared incoming-edge choice for all Phis at a Region. Track which data nodes are pinned. |
| §7, types and pessimistic optimizations | Relate abstract type facts to concrete values, justify folding and identities on the admitted primitive semantics, and type multi-result producers and projections. |
| §8, more engineering concerns | Give Start, execution alternatives, projections, memory and I/O states, and calls typed interfaces. Prove ordering and the selected results for each supported stateful primitive. |
| §9, removing control information | Justify removing a computation’s control input under an explicit safety/speculation condition and reconstruct a legal execution order. Require guards for operations whose definedness depends on control. |
| §10, optimistic transformations | Define transfer functions for control and values, including loops. Prove sparse worklist convergence, agreement with the declared fixed point and sound use of the resulting facts. |
| §11, summary | Use the worked graphs as regression cases for the earlier obligations. |

### A Simple Graph-Based Intermediate Representation

| Workshop sections | Open Lean obligation |
| --- | --- |
| §1, introduction | Specify the shared SSA graph invariant and relate the initial graph to a typed CFG. |
| §§2.1–2.4, nodes, Regions, Phis, Ifs and projections | Type ordered ports and distinguish data and control. Give each incoming control occurrence its own index, including two transfers from the same block. Pair each Phi’s ordered inputs with those occurrences. Type projected results. |
| §2.5, memory and I/O | Model memory and I/O as explicit state values. Show that independent components can be separated only with a sound independence relation and that their recombination preserves observations. |
| §3, model of execution | Define control-token steps, branch selection and simultaneous Phi latching at joins and loop re-entry. Distinguish live graph cycles through merge/feedback from unsupported cycles among strict data dependencies. Relate node-level execution to ordered SSA execution. |
| §§4.1–4.5, implementation | Relate node identity to structural keys, retain ordered operand slots and prove use-def/def-use coherence through insert, replace and delete. Treat object layout and allocation speed as implementation details. |
| §5.1, optimizing through a peephole | Justify abstract value computation, identities and hash-consing, with a precondition for each fold. Prove replacement preserves graph well-formedness and behavior. |
| §§5.2–5.3 and §§6–7 | Treat benchmark results as historical evidence and the related-work comparison as context for the graph invariant. |

### Rice dissertation

| Dissertation chapters | Open Lean obligation |
| --- | --- |
| Ch. 1, introduction | Fix the source/target semantics, permitted optimization observations, and intermediate graph invariant. |
| Ch. 2, optimistic assumption | Justify what the initial optimistic element says about unknown values and paths. Prove that iterating cyclic equations yields facts safe to use at the chosen fixed point. |
| §§3.2–3.5, framework, constant propagation and solving | Instantiate a monotone finite-height framework with primitive transfer functions and a concretization. Establish termination and greatest fixed point in the thesis’s order, or give the order-dual statement explicitly. |
| §§3.6–3.9, unreachable code, combined analyses and GVN | Prove value facts and executable-edge facts mutually sound, with Phi transfer over executable edges. State when the combined result improves separate analyses. Use the TOPLAS article’s §§2–4 for the framework and iteration, §§5–6 for the reachability/constant product and profitability, and §7 for adding value numbering. |
| §§4.1–4.5, efficient combined algorithm | Specify Hopcroft-style partition refinement, splitting and the effects of executable inputs and constants. Prove the optimized solver computes its specified partition and analysis facts. Keep the complexity bound as a separate theorem with a cost model. |
| §§4.6–4.11, identities and using the partition | Handle subtraction/comparison, leader/follower identities, and equal-input Phi/Max cases under explicit hypotheses. Prove the resulting equivalences before replacing uses and scheduling. Record any congruences the solver intentionally misses. |
| Ch. 5, experimental data | Preserve the link to the reported ILOC experiments and leave benchmark reproduction outside semantic correctness. |
| §§6.1–6.4, optimizing without the global schedule | Separate control removal and graph rewrites from CFG extraction, legal placement and schedule heuristics. Use the PLDI rows below for the shared scheduler proof. |
| §§7.1–7.3, parser design and peephole optimizer | Specify current bindings, incremental use-def edges, incomplete labels/loops, Phi insertion and the contract for each rewrite while parsing. Later pruning of redundant Phis needs its own theorem. |
| §§7.4–7.5 and Ch. 8 | Carry forward worked cases and limitations. The historical speedups and future directions serve as context. |
| App. A §§A.1–A.3, IR design and engineering | Reuse the report/workshop graph and rewrite invariants. Include abstract types and argument ordering in the interface. |
| App. A §§A.4–A.5, one-tier execution and engineering | Reuse control flow, Phi latching, If, Start and projections. Treat state and subroutine effects as explicit boundaries. |
| App. A §§A.6–A.7 | Retain the comparison with related representations. Require a translation theorem for any claimed equivalence. |

### Global Code Motion/Global Value Numbering

| PLDI sections | Open Lean obligation |
| --- | --- |
| §§1–1.2, motivation and representation | Define the floating/pinned distinction and admissible graph domain. Identify which conclusions hold for reducible CFGs and what requires different loop information. |
| §2 and §2.1, GCM, dominators and loops | Recover reachable control and certify the dominator tree and loop information on the supported shape. Specify the handling of unreachable code and a reachable loop with no exit. |
| §2.2, schedule early | Each floating node’s placement must be dominated by its operand definitions and permitted by its safety/control constraints. Pinned nodes retain their required placement. The paper’s footnote 6 allows faulting operations to move later under partial correctness. A profile that observes faults needs a stronger condition. |
| §2.3, schedule late | Compute the common dominator of uses, interpreting a Phi use on its corresponding incoming edge. Prove the feasible placement interval and that moving a computation does not introduce a trap or unwanted effect. |
| §2.4, selecting a block | Prove legality for any chosen block in the interval, including intra-block order. Then verify the shallow-loop/deep-dominator choice independently of performance claims. |
| §§3–3.2, value numbering | Prove representative substitution for equal keys and the stated algebraic identities, including worklist invalidation. Graph replacement can leave nodes without a legal old placement. Compose the replacement proof with schedule reconstruction. Treat stronger cyclic congruence discovery as the separate thesis chapter 4 obligation. |
| §§4–5, experiments and conclusions | Use the examples as regressions and keep the ILOC comparisons empirical. |

The HotSpot paper illustrates a richer instantiation. §§3–4 describe
ordered inputs, incremental graph construction and `Ideal`, `Value`,
`Identity` and GVN. §8 adds iterative passes and conditional constant
propagation. §§9–11 cover machine-node selection, scheduling and local
ordering. In particular, §10 accounts for load/store anti-dependence.
§§2, 5–7 and 16–18 supply JVM-specific runtime, deoptimization, exception
and numeric requirements for a future HotSpot profile. Click’s reply
identifies anti-dependence as a gap in the thesis scheduler. Use the
pinned Simple chapter 13 for the tutorial algorithm and its exact chapter
number. [HotSpot paper][hotspot] · [Click’s reply][reply] · [Simple 13][s13]

## Official Simple implementation

The primary executable reference is the Java tutorial at
`f0a6c6757a795b8e186de0076836a87acef59fa7`. The chapter README, node and
optimizer implementations, and tests at that commit define each fixture’s
profile. Use the chapter sources when the top-level synopsis lags the
chapter. For example, chapter 15 documents runtime array safety checks.
The Japanese READMEs, linear-history branch, graph viewer and printers
provide alternate presentations of the same work. The roadmap records
future features. The chapter 8 evaluator and chapter 13 scheduler are
concrete entry points for differential fixtures. [Java snapshot][simple] ·
[Chapter 15][s15] · [Roadmap][roadmap] · [Evaluator][evaluator] · [Scheduler][scheduler]

| Java chapters | Open Lean obligation or scope boundary |
| --- | --- |
| [1][s01]–[4][s04] | Start and Return, integer input and arithmetic, local binding updates, comparisons and folding. Use constants, an expression with sharing and a nonconstant argument as first fixtures. Specify the chapter’s arithmetic conventions before admitting division or any other non-total operation. |
| [5][s05]–[6][s06] | Lower branch projections and current bindings to Region/Phi joins. Check dead input pruning changes the Region and every attached Phi in step. A diamond with different results on the two paths distinguishes the indices. |
| [7][s07]–[8][s08] | Specify eager loop Phis, lazy creation, and the edge contributions of break and continue. Prove that graph evaluation uses the previous iteration’s values for a simultaneous Phi update. Include zero iterations, feedback, and a reachable loop with no finite return. |
| [9][s09] | Prove equality for graph-aware node keys and local rules. For iterative peepholes prove that invalidation covers all necessary users, including registered distant dependencies. State convergence for the supported rules and worklist policy. |
| [10][s10]–[12][s12] | Begin with a whole-memory state and struct allocation, field initialization, loads, stores and null refinement. Add alias classes and lazy split/merge using `MemMerge`, `MemPhi` and `BulkMemPhi`. Prove projection and reassembly against whole memory, including joins and loop feedback. Extend the shape invariant for references and forward/recursive struct declarations. |
| [13][s13] | Instantiate the pure scheduling proof, then prove the memory-aware extension. The `Never` edge makes an exitless loop visible to a backward scheduler walk. Prove that the edge cannot take a return and that alias-filtered anti-dependences preserve load observations across and within blocks. Test an overwrite of the same field and a store to an independent field. |
| [14][s14]–[17b][s17b] | Specify truncation, range transfers and floating-point rounding, then array allocation, addressing and bounds-check behavior. Track constructor initialization and read-only reference permissions, including deep views. Lower syntax sugar by desugaring with the same observation. [17a][s17a] gives the permission boundary. |
| [18][s18] | Type function entry/exit, call/result projections, memory threading and known targets. Prove call/return simulation first. Give recursion and inlining separate simulation statements covering continuation and state. |
| [19][s19]–[22][s22] | Track machine-node selection (including memory), allocation/spills, encoding, target ABI and FFI as downstream correctness boundaries. Pin an ISA and ABI per later backend slice. The ISA emitters, ELF layout and native Hello World are outside the initial IR proof sequence. |
| [23][s23] | Prove the admitted cyclic type comparison/rewriting invariant, method lookup and final-field facts. Keep register allocator tuning with the backend. |
| [24a][s24a]–[24b][s24b] | Instantiate the sparse control/value solver intraprocedurally. Extend reachability across discovered call targets, recursion and unknown callers with conservative summaries. Keep the analysis theorem separate from rewriting on the result. |
| [25][s25] | Specify provisional SSA before types are complete. Prove that resolution and graph updates preserve binding, conversion and branch-fact obligations, and give a precise rejection condition for an unresolved graph. |
| [26][s26]–[27][s27] | Prove that private constructor state becomes observable only at publication. Track escape/exposure through memory, callbacks, known and unknown callers, and the Start/Stop boundary. |
| [28a][s28a]–[28b][s28b] | Specify lazy initialization order and the rejection rule for cycles that would observe unfinished state. Give separate compilation a linking and shared-state contract, including effects of unknown code. |
| [29][s29]–[31][s31] | Carry forward partial-object completion and privacy rules, stream I/O ordering, numeric defaults and intrinsic semantics where they change the observed IR. Diagnostics, text formatting, register-allocation tuning and graphics/audio demos stay outside the graph proof sequence unless used as boundary fixtures. |

### Ports and other implementations

| Official repository and pin | Evidence and use |
| --- | --- |
| [Simple-Go][go], `37cc338992bcaf4a8a83fd5fbef52a67dc088884` | Chapters 1–4 on disk. The README explicitly describes a non-exact port and adds graph/peephole directives. Compare early arithmetic and bindings on the common subset. Exclude the directives from source-language semantics. |
| [Simple-Rust][rust], `d75781d1c516805d3042e66ddbd48a9b34fc6878` | The README claims chapter-17 parity at [Java `fd5178dbf4174933798ecbfbfe06fe35de0337c4`][rust-baseline]. The tree has a graph evaluator, a scheduler and chapter tests. Use matching pre-split chapter cases for differential fixtures. |
| [Simple-Cpp][cpp], `49877551b4ee91c53d799523f15810470a16abbb` | README claims chapter-13 parity. The tree has directories through Chapter18, with evaluator and scheduling files in later directories. Parity beyond the README claim is unverified. Use chapter-13 scheduler and evaluator cases after checking the common profile. |

Compare port behavior by normalizing node IDs and comparing ordered
inputs and observations on matching fixtures. Record differences in
parsing, arithmetic, scheduling and memory as port-specific deltas.
A port result supplies regression evidence. Treat semantic parity as a
separate claim that needs a translation or an agreed common reference.
The organization’s `.github` repository is profile material. Current
HotSpot C2, Graal and V8 are separate implementation targets with distinct
opcodes, effects and runtime contracts. Their equivalence to Simple remains
outside this plan. [Official organization][org]

## Existing Lean results

| Evidence in Silmaril | Reuse and remaining gap |
| --- | --- |
| [λRTL CFG theorems][cfg-thms] and [forward CFG validation][cfg-validation] | `run_flatten` and `run_eq_toRegion` connect the forward block model with region execution. The validator covers coherent renamings and a guarded entry contraction. Reuse the proof pattern for control extraction. Sea of Nodes adds unordered floating nodes, predecessor-indexed Phis and cyclic control. |
| [SSA and λRTL with loops][ssa], [loop theorems][loop-thms] and [machine C-backend construction][machine-construct] | `Region.evalObs_eq_evalSSA_of_isSSA` gives lexical/store agreement in the loop model with its hypotheses. The machine construction gives maximal SSA by passing every register to each block, with a simulation in its own RTL setting. Demand-driven Phi placement remains open here. Its graph/RTL types belong to the Machine region. |
| [λSSA forwarding cycles][cycle-cuts] | `exists_bounded_cut` and `iterate_fold` cover finite all-recurrent forwarding tables. Use them as a model-specific comparison for exitless control. SoN needs a graph-level observation theorem for feedback and for the synthetic scheduling edge. |
| [RVSDG graph and term theorems][rvsdg-thms], [acyclic λSSA lowering][rvsdg-acyclic] and [acyclic-body θ wrapper][rvsdg-theta] | `Graph.toGraph_toTerm` and `Term.toTerm_toGraph` cover numbered RVSDG graphs. The lowering and `denoteRegion_join` cover the generated typed single-entry/single-join acyclic grammar. The θ wrapper checks a specific single-loop shape. Translate admitted SoN shapes through these interfaces. A Region/Phi pair becomes a typed join in λSSA, and γ and θ carry scoped interfaces and loop state. General SoN control graph recovery is open. |
| [RVSDG explicit state splice][rvsdg-splice] and [interprocedural RVSDG][rvsdg-calls] | The splice preserves finite exit, payload and exact final token in its partial model, with a witness for the component boundary. The interprocedural development provides typed function and state interfaces. Start with one SoN state token and an explicit interface mapping. Alias partitions, scheduling anti-dependence, and translation of arbitrary call graphs require new obligations. |
| [MLIR Arith theorems][mlir-thms], [scalar profile][mlir] and [MLIR language reference][mlir-ref] | `Block.toLambdaSSA_hasType` and `Block.toLambdaSSA_eval_iff` cover the pure single-block scalar profile. Compose through the same λSSA primitive interpretations for flag-free bitvector constants, add and multiply. Multi-block SSACFG regions, typed block arguments, scoped regions with effects and MLIR graph regions require their own admission and preservation theorems. |
| [Guarded e-graph rebuild][egraph], [dataflow iteration][dataflow] and [checked pass contracts][compiler] | The e-graph has acyclic term witnesses and guarded merges. The iteration layer proves convergence of round-robin iteration to the least fixed point under its hypotheses. Checked passes show how to package admission and semantic preservation. A sparse worklist and SoN’s keys, facts and rewrites on control-aware cyclic graphs require separate proofs. |

## Proof sequence

Each slice should publish its admitted input profile, source anchors,
observable relation, definitions and theorem headers, and a small fixture
that exercises the distinguishing invariant. Record the exact upstream
chapter path and revision for executable fixtures. A fixture covers a
specific example. Mark an obligation covered once a public theorem proves
it at the stated profile. Record the first rejected extension alongside it.

1. **Graph invariant and pure execution.** Start with one function,
   Start/Return, ordered typed ports, total modular integer primitives, If
   projections, Region and simultaneous Phi. Begin with a diamond and
   acyclic strict data dependencies. State validity of IDs and ports,
   arity/type checks, inverse-use coherence if cached, and correspondence
   between incoming control slots and Phi operands. Define execution on
   admitted inputs and prove its determinism and invariance under coherent
   node renaming. Exercise both branches and reject a stale or misaligned
   Phi input. This covers the common structural target of Quads §§4–6,
   IR ’95 §§2–3, thesis App. A.2–A.4 and Simple 1–6.

2. **SSA construction and readback.** For a typed pure acyclic SSA fragment,
   prove a graph construction preserves finite exit and payload in both
   directions. Give checked readback for an explicitly scheduled graph and
   relate the two translations on the admitted image up to coherent
   renaming and discarded dead pure nodes. Include two occurrences from the
   same predecessor with different arguments. Then add one reducible
   single-entry loop, with a theorem for previous-activation Phi values and
   a separate statement relating absence of finite returns. Add eager and
   lazy construction only after the closed graph semantics is fixed.
   [Rice dissertation][thesis] · [Simple 7][s07] · [Simple 8][s08]

3. **Pure rewrites and scheduling.** Prove one peephole and equal-key
   substitution before iterative GVN. Compare a successful rewrite with a
   case where identical operands are insufficient because the primitive
   profile or control guard differs. In a scheduling PR, check CFG
   extraction, pinned placement, early/late bounds and Phi use sites.
   Prove schedule soundness against the graph semantics, then implement
   the loop-depth choice. Test a floating definition used on a Phi edge
   and a pinned operation that would be unsafe to hoist. An exitless
   loop must keep its observable behavior even if the scheduler uses
   synthetic control internally. [PLDI paper][gcm] · [Simple 9][s09] ·
   [Simple 13][s13]

4. **Restricted RVSDG and MLIR bridges.** On the pure slice, use the same
   typed λSSA observations on both sides. Start with the generated
   acyclic grammar for γ and the pure scalar single-block MLIR profile.
   Prove correspondence for both arms of a diamond and for shared
   arithmetic values. Add θ through the existing loop wrapper after the
   loop slice. Require an explicit decomposition or a certified
   recognizer for reverse translation from a larger graph. [Acyclic λSSA
   lowering][rvsdg-acyclic] · [θ wrapper][rvsdg-theta] · [MLIR scalar
   profile][mlir]

5. **State and scheduling.** Relate one ordered graph memory value to a
   reference heap and observe the returned value and final heap. Add a
   typed state mapping for the RVSDG token boundary. In later PRs, prove
   split/merge and alias disjointness, then load/store motion with the
   anti-dependence constraints. Use same-field, disjoint-field and
   memory-Phi cases to distinguish the required edges. Extend observations
   to traps, calls and I/O with the relevant contracts. [Simple 10][s10] ·
   [Simple 11][s11] · [Simple 13][s13] · [RVSDG state splice][rvsdg-splice]

6. **Optimistic and interprocedural analysis.** Prove a finite,
   intraprocedural SCCP solution for the admitted primitive lattice and
   executable edges. Then prove pruning and folding sound from the
   solution, including a loop where reachability changes a Phi fact.
   Develop combined congruence refinement, call-target discovery, and
   private/escaping state as later slices. [TOPLAS article][combining] ·
   [Rice dissertation][thesis] · [Simple 24a][s24a] · [Simple 24b][s24b]

Put the IR and its semantics under the SSA region, subject to the allowed
imports in [regions.toml][regions]. Use `Defs.lean`/`Thms.lean` and the
matching proof modules. Take other topics through their public headers.
Prove the first slices in the existing SSA dependency direction. Put a
bridge that needs machine semantics on the side allowed to import SSA.
Each proof PR can add a targeted `make check CHECK_TARGETS=+…` command and
fixture, following the [repository instructions][agents].

For the first slice, equality of finite typed return observations is
sufficient on the admitted pure acyclic fragment. Later steps need to state
what a trap, divergence, blocking, an external effect or a rejected graph
means in each model. In particular, absence of a finite return in a
`Part` model can identify neither the cause nor an external trace.
General irreducible control flow, arbitrary effectful RVSDG recovery,
MLIR dialect-specific undefined behavior, Java deoptimization and backend
validation stay open at the boundaries identified above.

[thesis]: https://hdl.handle.net/1911/16807
[thesis-pdf]: https://repository.rice.edu/server/api/core/bitstreams/c5ea1ab7-e6c6-41e7-8e06-3cd5b80aeccd/content
[quads]: https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf
[ir]: https://doi.org/10.1145/202529.202534
[ir-notices]: https://doi.org/10.1145/202530.202534
[ir-pdf]: https://www.oracle.com/technetwork/java/javase/tech/c2-ir95-150110.pdf
[gcm]: https://doi.org/10.1145/207110.207154
[gcm-notices]: https://doi.org/10.1145/223428.207154
[gcm-pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[combining]: https://doi.org/10.1145/201059.201061
[combining-pdf]: https://web.archive.org/web/20250916211010id_/https://dl.acm.org/doi/pdf/10.1145/201059.201061
[hotspot]: https://www.usenix.org/legacy/event/jvm01/full_papers/paleczny/paleczny.pdf
[braun]: https://doi.org/10.1007/978-3-642-37051-9_6
[braun-pdf]: https://pp.ipd.kit.edu/uploads/publikationen/braun13cc.pdf
[cytron]: https://doi.org/10.1145/115372.115320
[wegman]: https://doi.org/10.1145/103135.103136
[alpern]: https://doi.org/10.1145/73560.73561
[graal]: https://doi.org/10.1007/978-3-030-88885-5_8
[termgraphs]: https://doi.org/10.1145/3573105.3575673
[org]: https://github.com/SeaOfNodes/.github/blob/89ceafeec69c412f7bc4798e8145924c9f956060/profile/README.md
[easy]: https://www.dropbox.com/scl/fi/0ww4sgl3ynep9hhe3i4xn/EasySSA.pdf?rlkey=2cp78hzxke62flkmyneiebzoz&dl=1
[slides]: https://www.dropbox.com/scl/fi/cxykfvlzsmlcatyg6rlbt/SeaOfNodes.pdf?rlkey=z6o7y3rwr6atrejilcze6r8x0&e=1&dl=1
[simple]: https://github.com/SeaOfNodes/Simple/tree/f0a6c6757a795b8e186de0076836a87acef59fa7
[roadmap]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/docs/roadmap.md
[reply]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/ASimpleReply.md#complex-schedule
[rebase]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/docs/2026_REBASE/README.md
[evaluator]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java
[scheduler]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter13/src/main/java/com/seaofnodes/simple/GlobalCodeMotion.java
[go]: https://github.com/SeaOfNodes/Simple-Go/tree/37cc338992bcaf4a8a83fd5fbef52a67dc088884
[rust]: https://github.com/SeaOfNodes/Simple-Rust/tree/d75781d1c516805d3042e66ddbd48a9b34fc6878
[rust-baseline]: https://github.com/SeaOfNodes/Simple/tree/fd5178dbf4174933798ecbfbfe06fe35de0337c4
[cpp]: https://github.com/SeaOfNodes/Simple-Cpp/tree/49877551b4ee91c53d799523f15810470a16abbb
[cfg-thms]: ../../Silmaril/SSA/LambdaRTL/CFG/Thms.lean
[cfg-validation]: cfg-validation.md
[ssa]: ssa.md
[loop-thms]: ../../Silmaril/SSA/LambdaRTL/Loop/Thms.lean
[machine-construct]: ../../Silmaril/Machine/CBackend/RTL/Construct/Defs.lean
[cycle-cuts]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/WithConstructorSequencing/UnitSumSquare/Cycles/Automatic/Thms.lean
[rvsdg-thms]: ../../Silmaril/SSA/RVSDG/Thms.lean
[rvsdg-acyclic]: rvsdg-lambdassa-acyclic.md
[rvsdg-theta]: rvsdg-lambdassa-acyclic-theta.md
[rvsdg-splice]: rvsdg-numbered-splice.md
[rvsdg-calls]: rvsdg-interprocedural.md
[mlir-thms]: ../../Silmaril/SSA/MLIR/Arith/Thms.lean
[mlir]: mlir.md
[mlir-ref]: https://mlir.llvm.org/docs/LangRef/
[egraph]: ../guarded-egraph.md
[dataflow]: ../../Silmaril/Calculi/Dataflow/Thms.lean
[compiler]: compilers.md
[regions]: ../../regions.toml
[agents]: ../../AGENTS.md
[s01]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter01/README.md
[s04]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter04/README.md
[s05]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter05/README.md
[s06]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter06/README.md
[s07]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter07/README.md
[s08]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/README.md
[s09]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter09/README.md
[s10]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md
[s11]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter11/README.md
[s12]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter12/README.md
[s13]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter13/README.md
[s14]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter14/README.md
[s15]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter15/README.md
[s17a]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter17a/README.md
[s17b]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter17b/README.md
[s18]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter18/README.md
[s19]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter19/README.md
[s22]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter22/README.md
[s23]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter23/README.md
[s24a]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter24a/README.md
[s24b]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter24b/README.md
[s25]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter25/README.md
[s26]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter26/README.md
[s27]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter27/README.md
[s28a]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter28a/README.md
[s28b]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter28b/README.md
[s29]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter29/README.md
[s31]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter31/README.md
