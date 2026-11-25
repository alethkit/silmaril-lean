# Cambridge SPL chapter and exercise checklist

This checklist follows Peter Sewell’s *Semantics of Programming Languages*
notes for Cambridge Computer Science Tripos Part IB, 2025–26, dated
12 February 2026. The bibliography pins the PDF as `sewell2026semantics`.
See the [course index](cambridge.md) for the companion Part II courses and
the [operational guide](cambridge-operational.md) for build commands.
[Official notes][notes] · [Companion implementations][materials] · [Bibliography][bib]

**Checked** means a Lean judgment, theorem, or example covers the stated
item. **Scoped** marks a documented assumption, alternative representation,
or partial exercise. The checklist identifies missing fixtures and states
when a printed claim is refuted or a corrected conjecture remains open.
Lean names are relative to `Silmaril.Courses.Cambridge` unless given otherwise.

## Chapters and results

| Notes | Coverage |
| --- | --- |
| **1. Introduction**, pp. 8–12 | Course examples give structural operational rules and a transition system, including `L1.Step` and `L1.lts`. The warm-ups and history are exposition. [L1 rules][l1step] |
| **2. First imperative language**, pp. 13–32 | L1 syntax, finite integer stores, reduction and typing implement the collected definition. Theorems **1–7** map to `L1.Step.deterministic`, `progress`, `preservation`, `safety`, `infer_iff_hasType` with `typeable_iff_infer_isSome`, decidable `HasType`, and `HasType.unique`. `StepTree.toStep` certifies concrete derivations for Definition **1**. Rule induction uses the inductive `Step` relation. A separate L1 theorem identifying an explicit least closed set from Definition **2** and the search is outside this development. [Types and inference][l1typing] · [Metatheory][l1meta] · [Derivation search][l1printer] |
| **3. Induction and proofs**, pp. 33–48 | Lemmas **9–12** map to value terminality and the `Step`/`HasType` inversion families. Lemmas **13–14** and **16–17** map to typed value canonical forms. `L1.Step.store_domain` proves Lemma **15** pointwise. `preservation_by_typing` gives the alternate proof. Theorem **8**, the arithmetic-series illustration of induction, has no dedicated Cambridge fixture. [Inversion][l1inversion] · [Metatheory][l1meta] |
| **4. Functions**, pp. 49–68 | Named syntax, scope resolution retaining free names, alpha-equivalence, substitution, CBV, CBN, full beta, strict let and recursive functions. Theorems **18–19** and Lemma **20** map to `L2.progress`, `type_preservation`, and `L2.HasType.subst` / `beta`. Determinacy follows from `L2.Config.reduce_value_iff_step`. `L2.PureDenotation.Term.not_diverges` supplies the recursion-free, store-free result for Theorem **21** on the indexed pure fragment. Its hypothesis is a fragment derivation. The notes leave the proof details outside taught scope. [L2 course][l2] · [Metatheory][l2meta] · [Normalization on the fragment][l2adequacy] |
| **5. Data**, pp. 69–82 | L3 covers products, annotated sums, ordered records with distinct labels and mutable reference values. Definition **22** maps to `L3.StoreTyped`. Theorems **23–25** map to `L3.progress`, `preservation` and `safety`. Theorem **26** holds for the printed contexts at typed sources (`contextStep_iff_step_of_hasType`) and at arbitrary configurations with the location premise restored (`locationContextStep_iff_step`). `assignment_context_counterexample` refutes the literal untyped claim. Section 5.2 excludes recursive datatypes from L3. [L3 course][l3] · [L3 metatheory][l3meta] |
| **6. Subtyping and objects**, pp. 83–88 | Structural width, depth, permutation, function variance, products and reference invariance, plus the sum rule. `Subtyping.L3Subty`, `Typing.sub`, `progress`, `preservation`, and `safety` use L3 dynamics. `Subtyping.Examples.counterProgram_typed` checks a counter with private state. The object generator and method-reuse examples on pp. 86–87 lack dedicated checked derivations. [Subtyping guide][subguide] |
| **7. Concurrency**, pp. 89–97 | Checked shared-store interleaving, race schedules and primitive mutexes. `Concurrency.Mutex.step_iff_labelledStep` proves Theorem **27**. `conjecture28_false` refutes the printed all-stores form of **28** using an absent cell. `CoveredConjecture28` remains open. [Concurrency guide][conguide] · [O2PL counterexample][o2plex] |
| **8. Semantic equivalence**, pp. 98–102 | `L1.SemanticEquiv` compares returned value and store or joint divergence. `L1.Context.preservesEquiv` proves Theorem **29**. `L1.SemanticEquiv.seq_assoc` and `cond_seq` prove **30–31**. `conjecture32_counterexample` refutes **32**. `L3.ContextualEquiv` covers Definition **33** and contextual closure. Slide 256’s stateful-function comparison lacks a checked fixture. Slides 257–258 use a temporary pointer-equality extension. [Equivalence guide][equivguide] · [L1 laws][laws] · [L3 contexts][l3equiv] |
| **9. Semantics in practice** and **10. Epilogue**, pp. 102–103 | Historical examples, aims and design discussion. |
| **Appendices A–C**, pp. 105–126 | The official L1 OCaml, SML and Java implementations accompany the Lean reduction, derivation-printing and type inference counterparts. The host implementations remain external references. [Official materials][materials] · [L1 exercises][l1ex] |
| **Appendix D**, pp. 127–136 | Proof background with connective rules, the regular-language pumping lemma and sequent calculus. The appendix has no dedicated Cambridge Lean module. [Appendix D][notesD] |

## Exercises

The checklist covers the numbered exercises in the pinned notes. The
external Tripos revision questions remain separate.

### L1 rules and proofs

[Exercises 1–12, p. 31](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=31) · [Exercises 13–18, p. 48](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=48)

| Exercise | Coverage |
| --- | --- |
| **1** Factorial as L1 | **Checked for the requested program**, `L1.Exercises.factorial`, `factorial_has_type` and `factorial_initial_lookup` in `OneToThree`. No general factorial-correctness theorem for this L1 program. The separate Part II IMP factorial result concerns a different AST. [1–3][l1one] |
| **2** All steps of the two assignments | **Checked.** `assignment_step1`–`assignment_step5`, `assignment_trace`, `assignment_result_lookup`. [1–3][l1one] |
| **3** First four steps of the first slide-22 L1 example | **Checked.** `lecture_step1`–`lecture_step4` and `lecture_first_four_steps`. [1–3][l1one] |
| **4** Change operand evaluation order and distinguish it | **Scoped implementation, checked trace.** `EvalOrder`, `VariantStep`, `reduceWith`, `left_order_result`, `right_order_result` check the Lean counterpart and differing stores. [Variants][l1variants] |
| **5** Change assignment/sequence result rules and distinguish them | **Scoped implementation, checked trace.** `AssignResult`, `integer_assignment_step`, `integer_sequence_step`, `original_integer_sequence_stuck`. [Variants][l1variants] |
| **6** Match machine integers | **Scoped.** `MachineIntegers.Step` and `reduceConfig` model `BitVec w` wraparound and signed comparison with `overflow_step`, `overflow_interpreter` and `signed_comparison`. The actual overflow/exception behavior of each companion host is outside that theorem. [Machine integers][l1machine] |
| **7** Assignment typing | **Checked.** `assignment_type_derivation`. [Typing examples][l1typingex] |
| **8** Lecture example typing | **Checked with harmless environment weakening.** `lecture_type_derivation` uses the stated three-location environment, which includes one unused cell. [Typing examples][l1typingex] |
| **9** Preservation for the value-returning assignment variant | **Checked.** `old_assignment_typed`, `old_assignment_reduces`, `old_assignment_result_not_unit`, revised `ValueHasType`, and `value_assignment_preservation`. [Variant typing][l1vartyping] |
| **10** Revise the inference implementation | **Scoped Lean counterpart.** `inferValue`, `inferValue_iff_hasType`, `revised_inference_examples`. [Variant typing][l1vartyping] |
| **11** Host language, reference interpreter and L1 evaluation order | **Partial.** `original_operator_order_trace` and `sequence_left_first_trace` check L1. The companion implementations explicitly implement left-before-right object-language steps for these forms. The comparison with each host's own operand evaluation and an executable cross-host check are outside the checked artifact. [Lean examples][l1order] · [Reference sources][materials] |
| **12** Print a rule derivation or show search failure | **Checked for the reduction option in the exercise.** `searchConfig`, `StepTree.toStep`, `searchConfig_sound`, `printStep`, `malformed_addition_search_fails`. The exercise offers reduction or typing. The Lean exercise chooses reduction, certifies success, and supplies a stuck example. [Derivation printer][l1printer] |
| **13** Determinacy cases | **Checked.** `L1.Step.deterministic`. [Determinacy][l1det] |
| **13.5** Operational and typing inversion | **Checked.** `Step.binary_inversion`, `Step.seq_inversion`, `Step.cond_inversion` and the rest of the `Step` / `HasType` inversion families. [Inversion][l1inversion] |
| **14** Why nondeterministic operand order breaks determinacy | **Checked.** `NondeterministicStep`, `nondeterministic_operator_counterexample`, `nondeterministic_not_determinate`. [Determinacy][l1det] |
| **15** L1 progress | **Checked.** `L1.progress`. [L1 metatheory][l1meta] |
| **16** L1 preservation | **Checked.** `L1.preservation`. [L1 metatheory][l1meta] |
| **17** Preservation by induction on typing | **Checked.** `L1.preservation_by_typing`. [Alternate proof][l1presby] |
| **18** Uniqueness of typing | **Checked.** `L1.HasType.unique` and `unique_by_rules`. [L1 metatheory][l1meta] |

### L2 functions and interpreters

[Official exercise text, p. 68](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=68)

| Exercise | Coverage |
| --- | --- |
| **19** Five free-variable sets and alpha-invariant ASTs | **Checked.** `L2.Exercises.FreeVariables.first_freeVars` / `first_tree` through `fifth_freeVars` / `fifth_tree`. [L2 exercises][l2free] |
| **20** Three substitutions | **Checked.** `L2.Exercises.Substitution.first`, `second`, and `third`, with extra capture regressions. [L2 exercises][l2substex] |
| **21** Typing and untypability | **Checked.** `L2.Exercises.TypingDerivations.badConditional_untypable`, `shadowing_hasType`, `shadowing_tree`. [L2 exercises][l2typeex] |
| **22** First-order functions with fully saturated calls | **Checked as an exercise design.** `L2.Exercises.FirstOrder.HasType`, `HasType.call_saturated`, `partial_call_untypable`. [L2 exercises][l2first] |
| **23** Different CBV/CBN Boolean answers, and whether this can happen without store | **Partial.** `L2.Exercises.EvaluationStrategies.value_trace` and `name_trace` prove opposite Boolean answers with a cell. The no-store question remains unchecked. The separate divergence example answers a different question. [Strategy witnesses][l2strategies] |
| **24** Typed substitution | **Checked on resolved terms.** `L2.HasType.subst` and `beta`. [L2 metatheory][l2meta] |
| **25** L2 preservation | **Checked.** `L2.type_preservation` preserves type, closedness and coverage. [L2 metatheory][l2meta] |
| **26** Adapt interpreter to CBN and compare | **Scoped Lean counterpart with checked cases and general one-step correspondence.** `Config.reduce_name_iff_step` and `CallByNameInterpreter.name_matches_exercise23`, `name_runs_argument_twice`, `name_discards_divergence`, `recursiveSum_name` and the corresponding CBV cases. [CBN proof][l2name] · [Examples][l2cbnex] |
| **27** Closure interpreter | **Covered at implementation and example level.** `L2.evalClosureFuel`, `evalClosureGround`, and `Exercises.Closures.lexical_closure`, `recursion_closure`, `store_closure` with substitution results. A general correspondence theorem for this executable closure interpreter is absent. The adequate relational environment model covers recursive closures and loops. The executable fuelled interpreter has checked examples. [Relational L2 denotation][l2denotguide] [Closure evaluator][l2closure] · [L2 exercises][l2closureex] |

### L3 data and references

[Official exercise text, p. 82](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=82)

| Exercise | Coverage |
| --- | --- |
| **28** L3 preservation | **Checked.** `L3.preservation` and `preservation_steps`. [L3 metatheory][l3meta] |
| **29** Labelled variants | **Missing design exercise.** The collected language provides binary sums and labelled records. [Notes p. 82][notes5ex] |
| **30** ML-style exceptions | **Missing design exercise.** No module checks raise/handle typing and reduction or nested handler examples. [Notes p. 82][notes5ex] |
| **31** Extend the implementation to all of L3 | **Partial.** Named/resolved parsing and `L3.Config.reduce` cover the complete one-step grammar. `reduce_sound` and `reduce_exists_iff_step_exists` certify the selected successor, including allocation. A checked executable type checker and a full driver for the §4.5 workflow remain missing. [L3 reducer][l3interp] · [Official L2 implementation][l2sml] |

### Subtyping and objects

[Official exercise text, pp. 87–88](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=87)

| Exercise | Coverage |
| --- | --- |
| **32** Four subtyping cases | **Checked.** `nestedSingleton_typed` derives (1)'s `{p:{}}`; `nestedProjectionFunction_typed` derives (2)'s `x.q.p` lambda; `missingFieldArgumentFunction_untypable` rules out every type for the whole lambda in (3); `reorderedArgumentFunction_typed` checks (4). [L3 derivations][subl3ex] |
| **33** Both unsafe reference variances | **Checked.** `covarianceProgram_typed`, `contravarianceProgram_typed`, their `*_trace` lemmas, and `missingField_stuck`. [Reference examples][subref] |
| **34** Sum subtyping | **Checked.** `Subty.sum`, `L3Subty.sum_inv` and `widenedSumMatch_typed` / `widenedSumMatch_trace`. [Rules][subrules] · [L3 derivations][subl3ex] |
| **35** Typing for let and let rec with subtyping | **Checked.** The `Subtyping.Typing` let/let-rec constructors use extended typing in the premises, with `Typing.sub`. [Judgment][subtyping] |
| **36** Progress with subtyping | **Checked.** `Subtyping.progress`. Preservation and safety are also checked. [Subtyping modules][sub] |

### Concurrency

[Official exercise text, p. 97](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=97)

| Exercise | Coverage |
| --- | --- |
| **37** Compare SPL mutexes and C&DS | **Scoped to the selected bit.** `Mutex.Comparison.acquire_iff`, `release_iff`, `held_attempts` check action effects and held behavior. The guide describes Java reentrancy and the distinction between spinning, blocking and try-lock. [Concurrency guide][conguide] |
| **38** Necessity of all four O2PL conditions | **Checked checked counterexamples.** `protection_necessary`, `terminal_release_necessary`, `two_phase_necessary`, `increasing_order_necessary` in `Mutex.OrderedTwoPhase.Examples`. [O2PL examples][o2plex] |
| **39** Prove the O2PL conjecture | **Refuted as printed.** The covering-store version remains open. [O2PL examples][o2plex] |
| **40** Unix-style threads and communication | **Checked as a design exercise.** `Concurrency.UnixThreads` supplies IDs, fork/join, shared cells and asynchronous FIFO channels. The checks include `Step.preserves_wellFormed`, `Examples.fork_send_receive_join` and `fifo_trace`. [Unix-style threads][unix] |

### Semantic equivalence

[Official exercise text, p. 102](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=102)

| Exercise | Coverage |
| --- | --- |
| **41** Cover the other L1 congruence cases | **Checked.** `L1.Context.preservesEquiv` proves all context frames. [Congruence][cong] |
| **42** Exchange sequences with disjoint location typings | **Checked.** `L1.SemanticEquiv.seq_comm_of_disjoint` works under the union and preserves the treatment of other locations. [Disjoint stores][disjoint] |
| **43** Distinguish L3 assignments of zero and one | **Checked with a named free reference.** `L3.ContextualExamples.write_zero_not_equiv_write_one` uses a closing allocator and a read that chooses return or divergence, independent of the actual fresh address. [L3 distinguishing context][l3equivex] |

## Repository integration

- The L1–L3 byte parsers and canonical printers have checked source-domain
  round-trips and injectivity. L3’s `Concrete.Exact` fixes one spelling
  classification for variables and labels across terms, types and
  annotations, following the categories in §§5.2 and 5.5. The original
  byte profile also remains available. An independently specified
  ordinary-precedence grammar correspondence and a full L2→L3 grammar
  and operational embedding remain separate proof obligations.
  [L1/L2 syntax][con12] · [L3 syntax][con3]
- The structural AST codecs cover named L1–L3 terms and types and resolved
  L2/L3 terms. The wire bridges prove recovery from canonical UTF-8 JSON
  and S-expression bytes. Operational adapters and typed step and finite
  may-return specifications use full configurations, with checked
  satisfaction translations. [AST codecs][codecs] · [JSON bytes][jsonb] ·
  [S-expression bytes][sexpb] · [Operational adapters][opinst] ·
  [Step specifications][stepguide] · [May-return specifications][retguide]
- The syllabus’s core concerns operational semantics. The L1/L2/L3
  denotational fragments, the L1 LetIter compiler relation, and prospective
  game models and machine or Wasm backends are extensions. The Cambridge
  Part II courses have their own coverage guides.
  [Cambridge courses](cambridge.md) · [Integration guide][integration] ·
  [L2 denotation][l2denotguide] · [L3 denotation][l3denotguide]

[bib]: ../../references.bib#L383-L389
[codecs]: cambridge-ast-codecs.md
[con12]: cambridge-concrete.md
[con3]: cambridge-l3-concrete.md
[cong]: ../../Silmaril/Courses/Cambridge/SemanticEquivalence/Congruence.lean
[conguide]: cambridge-concurrency.md
[disjoint]: ../../Silmaril/Courses/Cambridge/SemanticEquivalence/Disjoint.lean
[equivguide]: cambridge-semantic-equivalence.md
[integration]: cambridge-integration.md
[jsonb]: cambridge-json-bytes.md
[l1det]: ../../Silmaril/Courses/Cambridge/L1/Metatheory/Determinacy.lean
[l1ex]: ../../Silmaril/Courses/Cambridge/L1/Exercises
[l1inversion]: ../../Silmaril/Courses/Cambridge/L1/Metatheory/Inversion.lean
[l1machine]: ../../Silmaril/Courses/Cambridge/L1/Exercises/MachineIntegers.lean
[l1meta]: ../../Silmaril/Courses/Cambridge/L1/Metatheory
[l1one]: ../../Silmaril/Courses/Cambridge/L1/Exercises/OneToThree.lean
[l1order]: ../../Silmaril/Courses/Cambridge/L1/Exercises/EvaluationOrder.lean
[l1presby]: ../../Silmaril/Courses/Cambridge/L1/Metatheory/PreservationByTyping.lean
[l1printer]: ../../Silmaril/Courses/Cambridge/L1/Exercises/DerivationPrinter.lean
[l1step]: ../../Silmaril/Courses/Cambridge/L1/Reduction.lean
[l1typing]: ../../Silmaril/Courses/Cambridge/L1/Typing.lean
[l1typingex]: ../../Silmaril/Courses/Cambridge/L1/Exercises/TypingDerivations.lean
[l1variants]: ../../Silmaril/Courses/Cambridge/L1/Exercises/Variants.lean
[l1vartyping]: ../../Silmaril/Courses/Cambridge/L1/Exercises/ValueAssignmentTyping.lean
[l2]: ../../Silmaril/Courses/Cambridge/L2
[l2adequacy]: ../../Silmaril/Courses/Cambridge/L2/Denotation/Adequacy.lean
[l2cbnex]: ../../Silmaril/Courses/Cambridge/L2/Exercises/CallByNameInterpreter.lean
[l2closure]: ../../Silmaril/Courses/Cambridge/L2/ClosureInterpreter.lean
[l2closureex]: ../../Silmaril/Courses/Cambridge/L2/Exercises/Closures.lean
[l2denotguide]: cambridge-l2-denotational.md
[l2first]: ../../Silmaril/Courses/Cambridge/L2/Exercises/FirstOrder.lean
[l2free]: ../../Silmaril/Courses/Cambridge/L2/Exercises/FreeVariables.lean
[l2meta]: ../../Silmaril/Courses/Cambridge/L2/Metatheory
[l2name]: ../../Silmaril/Courses/Cambridge/L2/Metatheory/NameInterpreter.lean
[l2sml]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/L2/
[l2strategies]: ../../Silmaril/Courses/Cambridge/L2/Exercises/EvaluationStrategies.lean
[l2substex]: ../../Silmaril/Courses/Cambridge/L2/Exercises/Substitution.lean
[l2typeex]: ../../Silmaril/Courses/Cambridge/L2/Exercises/TypingDerivations.lean
[l3]: ../../Silmaril/Courses/Cambridge/L3
[l3denotguide]: cambridge-l3-denotation.md
[l3equiv]: ../../Silmaril/Courses/Cambridge/SemanticEquivalence/L3.lean
[l3equivex]: ../../Silmaril/Courses/Cambridge/SemanticEquivalence/L3Examples.lean
[l3interp]: ../../Silmaril/Courses/Cambridge/L3/Interpreter.lean
[l3meta]: ../../Silmaril/Courses/Cambridge/L3/Metatheory
[laws]: ../../Silmaril/Courses/Cambridge/SemanticEquivalence/Laws.lean
[materials]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/materials.html
[notes]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf
[notes5ex]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=82
[o2plex]: ../../Silmaril/Courses/Cambridge/Concurrency/Mutex/OrderedTwoPhase/Examples.lean
[opinst]: ../projects/operational-institutions.md
[retguide]: cambridge-return-specification.md
[sexpb]: cambridge-sexp-bytes.md
[stepguide]: cambridge-step-specification.md
[sub]: ../../Silmaril/Courses/Cambridge/Subtyping
[subguide]: cambridge-subtyping.md
[subl3ex]: ../../Silmaril/Courses/Cambridge/Subtyping/L3Examples.lean
[subref]: ../../Silmaril/Courses/Cambridge/Subtyping/ReferenceExamples.lean
[subrules]: ../../Silmaril/Courses/Cambridge/Subtyping/Rules.lean
[subtyping]: ../../Silmaril/Courses/Cambridge/Subtyping/Typing.lean
[unix]: ../../Silmaril/Courses/Cambridge/Concurrency/UnixThreads
[notesD]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=127
