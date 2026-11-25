# Python SOS implementation and acceptance

The [Python SOS design](python-sos.md) starts with one integer-return body and
a guarded Core comparison. The implementation scope here is the SOS of the
Python 3.7 profile in Köhl’s thesis, the source and runtime needed to exercise
that profile, and the corresponding rule presentations for Wasm 1.0 and Lime1.
Each increment identifies its judgments, entry conditions, observations and
proof interfaces. Record profile changes in the corresponding coverage rows.

## Increments

| Increment | Depends on | Acceptance evidence |
| --- | --- | --- |
| P1. Python integer body | Operational policy | Labelled small steps for literals, exact addition and return. Prove reachable-step determinism, progress, termination, exact return value and absence of UB for admitted inputs. Regressions distinguish missing entry, unsupported state and a defined exception. |
| S1. Positive rule derivations and institution | P1 for the first client | Support finite lists of judgment premises and induction on derivations. Prove derivation transport, satisfaction under reduct and preservation of ordered labels on a two-step run. Give the independent rule presentation of P1 and prove an iff with its typed steps. Compare judgment forms and theorem hypotheses against existing reachability calculi. |
| Policy and precision | P1, S1 | Prove the marker embedding, safe restriction and per-entry completion and inclusion lemmas from the design. Check exact and permissive profiles on a defined return, exception and stuck case. Distinguish finite may inclusion from termination preservation. |
| P2. Expression and statement rules | P1, S1 | Record every rule family in thesis §§4.3.1–4.3.2, including evaluation order, short-circuiting, loops, exceptions and pending cleanup. Check action and payload typing, terminal forms and both directions of the typed-step/derivation correspondence. |
| P3. Frames, stack and heap | P2 | Record every rule family in thesis §4.4. Compose local and active-exception state, calls, returns, generator suspension and resumption, load/store and fresh allocation. Prove consumed and visible action laws, preservation of untouched bindings and the allocator invariant. Carry the chosen residual frame and heap witnesses across each step when claiming run agreement. |
| P4. Values, primitives and runtime | P2, P3 | Cover Appendix B.1 and the runtime services of the profile. Pin host contracts for I/O, hashing and float behavior. Exercise unbounded integers, binary64 edge cases, code points including lone surrogates, collection operations, object protocols, argument binding and registry state. Prove stateless specialization and distinguish a host failure from a catchable Python exception. |
| P5a. Source syntax and scope | Python language reference | Build and test a versioned AST and its scope analysis independently of the core. Check whole-block name binding, declarations, nearest enclosing function, capture and forwarding, as well as the scope boundaries for classes and comprehensions. |
| P5b. Compilation | P5a, P2, P3 for its artifacts | Compile into named code and literal stores. Specify the parser boundary. Prove executable compilation agrees with an independent translation relation through the final stores. For compilation over a bootstrap store, prove name freshness, lookup preservation and old frame decoding. Check accepted and rejected source fixtures. |
| P6. Bootstrap and runner | P3, P4, P5b | Initialize compiled source over the selected runtime. Prove each executable transition and the bounded run sound, with ordered labels and a resumable residual state. Exercise return, uncaught exception, host fault, blocked diagnostics and fuel/time limits. State what the allocator chooses and what the relational semantics admits. |
| S2. Structural derivation correspondence | P3, S1 | Make finite term encodings, service witnesses and allocation choices explicit. Prove soundness and completeness for step and incoming response judgments, with projected actions and successors. Check both directions for source allocation and the supported stateless machine, including suspended frames. |
| S3. Symbolic search | S1, S2 for the Python client | State the solution semantics and guards for partial operators. Prove solver soundness, solution preservation and termination, and fair answer enumeration under the stated encodability or finite-representative conditions. Include a starvation example and a negative test for dropped definedness obligations. Check arithmetic, CCS and Turing-machine clients against the public thesis, then exercise a finite Python derivation. |
| W1. Wasm rule presentations | S1 | Present independent V1 and Lime1 pure and machine rules for the native profiles. Prove iff results for pure reduction and machine steps, finite/labelled runs, divergence and instantiation. Cover host outcomes, trap, calls, memory effects and start behavior. Grow a rule-family inventory from the first guarded Core comparison. |
| W2. Wasm transport and observations | W1 | Carry derivations through the existing V1-to-Lime1 and Lime1-to-Core maps. Prove forward transport with compatible hosts. State reflection on its actual store and host domain. Check which returned values, traps, residual state and divergent runs each adapter observes. Recover denotation agreement at an identified denotation boundary. |
| W3. Python/WIT contract | P3, P4, existing component call semantics | Prove a bounded integer-return/WIT u32 correspondence for an actual component call. Include a successful relational call witness, the driver’s outcome contract, observable traps and an overflow counterexample. Reuse the component, WIT and memory interfaces. |
| Corpus and release evidence | P6 for Python corpus replay, all rows for closure | Pin source selection, profile, input hashes, oracle versions and per-case bounds. Record per-case compiler and runtime classifications, exact output code points, resolved retries and unresolved cases. Track external CPython comparisons independently from SOS comparisons. Link each accepted row to theorem headers or reproducible tests and the revision where checks passed. |

P1 and S1 form the first vertical slice in the design. After S1, work on
Python rules, symbolic foundations and Wasm presentations can proceed on their
own boundaries. P4’s runtime-service work and P5’s compiler work should agree on
the core artifact and bootstrap interface before P6 joins them. An already
reviewed implementation can satisfy a row when its domain, statement and tests
cover the acceptance evidence.

## Existing interfaces

| Public interface | Reuse and remaining obligation |
| --- | --- |
| [Operational institutions](operational-institutions.md) and [operational policy](../../Silmaril/Semantics/Operational/Policy/Thms.lean) | Labelled edges, run transport, entry and safety already have APIs. S1 needs explicit positive premises and a derivation relation whose step agreement is proved independently. |
| [Reachability derivations](../../Silmaril/Logic/Reachability/Derivation/Thms.lean) and [rule systems](../../Silmaril/Logic/Reachability/RuleSystem/Defs.lean) | Compare rule instances and the role of premises before adding interfaces for symbolic proofs. |
| [Native Wasm 1.0 scalar](wasm-v1-intrinsic.md), [version injections](wasm-version-injections.md) and [Core operational institution](../../Silmaril/Wasm/Institution/Operational/Thms.lean) | Reuse typed reduction, existing guarded simulations and the Core encoding. The V1/Lime1 derivation interfaces need their own step, run and instantiation correspondence. |
| [Core entry](wasm-opsem-entry.md), [memory profile](../../Silmaril/Wasm/Execution/Core/MemoryProfile/Thms.lean) and [kernel memory](wasm-kernel-memory.md) | Reuse machine entry, memory operations and available read/write facts. P3 needs heap/reference laws, and W2 needs the simulation hypotheses for each retained observation. |
| [Compiler APIs](compilers.md) and [component semantics](component-semantics.md) | Use the existing translation and observation contracts where they match. P5’s artifact correspondence and W3’s component behavior require separate proofs. |

## Provenance and completion

Write the Lean definitions, proofs, generators and tests from public
specifications. Cite exact revisions or artifact hashes. Use the CC BY-SA 4.0
thesis to identify judgments and cite them, with original formalizations.
[Köhl thesis, arXiv v1](https://arxiv.org/abs/2109.03139v1)

The Python reference license covers documentation and identifies the separate
grant for examples. Apply the repository’s Wasm and SpecTec notices to material
derived from those pinned sources.
[Python reference license](https://docs.python.org/release/3.12.13/license.html)
[Wasm notices](../../NOTICES/WebAssembly-spec/README.md)
[SpecTec notices](../../NOTICES/spectec/README.md)

For the public research corpus, record the selection and check each fixture’s
source and licensing before redistribution. Use an explicitly supplied
upstream checkout where the historical corpus can be exercised without
bundling it. Use independently authored or verified redistributable fixtures
for continuous integration.
[Research corpus at its evaluation revision](https://github.com/koehlma/rigorous/tree/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python)

Every completed increment needs named proof statements with their actual
hypotheses, regressions for the claimed profile, the applicable `make check`
targets, and a transitive axiom audit for new proof entry points. Keep coverage
counts, corpus observations and universal theorems as separate evidence.
General source-to-execution adequacy, complete CPython compatibility and
unrestricted Wasm reflection require additional specifications and theorems.
