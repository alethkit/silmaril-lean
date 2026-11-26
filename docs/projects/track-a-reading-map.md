# Track A reading map

Track A gives a typed vocabulary for interactions, observation and refinement,
a finite primitive concurrency model, and two admitted SQLite storage cases.
The table identifies the observation point for each result and links to
the statements and checks.

## Reading order and evidence

| Question | Statements and checks |
| --- | --- |
| What does an interaction expose? | A request determines its response type. An exchange pairs a request with a completed response. `Coalgebra.observes_tau`, `observes_visible_loop`, `observes_handle_vis`, and `obsEq_iff_mutual_refines` cover silent steps, an infinite exchange path, stateful handling and refinement. The countdown regression has completed runs of every finite length and no infinite exchange path. [Interaction guide][interaction] · [Header][interaction-thms] · [Regression][interaction-check] |
| What does the guarded fragment add? | `Guarded.Forest.step_vis` checks erasure of a first-order, context-indexed visible step whose reply determines the next context. `WeakITree.observes_diverge` checks the delayed adapter's representation of weak-tree divergence by a silent self-loop. [Guarded header][guarded-thms] · [Weak-tree header][weak-thms] |
| What survives relabeling and signature change? | `Forest.observes_relabel` transports observations by direct image for signature maps with bijective response decoders. Requests may merge. The four institutions use the opposite signature category, and satisfaction checks inclusion in an allowed observation set. `tree_trace_satisfaction`, `tree_explicit_satisfaction` and `tree_catastrophic_satisfaction` relate forest satisfaction to the three trace bounds. The regression shows why dropping response bijectivity can introduce stuckness. [Institution guide][institution] · [Relabeling header][relabel-thms] · [Institution header][institution-thms] · [Regression][institution-check] |
| Where does Elgot iteration apply? | `loop_observes_infinite` witnesses a single path from compatible replies in the request-guarded loop. `interpret_guardedLoop`, `interpret_guardedLoop_naturality` and `interpret_nestedGuardedLoop` use the existing weak ITree fold into a lawful Elgot target under the stated `Small` hypotheses. [Iteration header][elgot-thms] |
| How is undefined behavior (UB) represented? | A finite tree observation ending in `returned none` retains its exchanges. `UB.atBoundary_ub_iff` witnesses such a run after projection to a single marker that drops its prefix. `collapse_eq_top_iff` and `val_collapse_of_safe` describe whole-row saturation and exactness on UB-free rows. `bind_eq_top_iff` locates UB in the first row or a reachable continuation row. [UB header][ub-thms] · [Boundary and relabeling][relabel-thms] |
| What is sequentially consistent (SC)? | `replay_iff` relates each finite primitive execution to its schedule. `classifyHistory_eq_some_iff` ties validation to generated executions, and a regression rejects a forged read that the raw classifier calls clean. `guarded_iff_filtered` equates ordinary guarded runs with clean raw runs. `racy_run_has_ub_prefix` and `raceUB_has_raw_run` connect raw executions to the first racing extension. The examples check a lock cycle with a separate completing schedule and a race-free run of SC atomic loads and stores that loses an update. [SC and race guide][sc] · [Header][sc-thms] · [Examples][sc-check] |
| When can a concurrent trace be projected? | `Interface.observedRun_inter` factors filtered observations while retaining a source execution witness. `Projection.happensBefore_eq` requires retained cross-thread edge endpoints and, for the mixed profile, coverage of intervening overwrites. `Projection.classify_eq` additionally requires conflict coverage. The examples hide a handoff, overwrite or conflict, and check that repeated labels map to distinct source occurrences. [Projection guide][sc-projection] · [Header][projection-thms] · [Examples][projection-check] |
| How are sequential interfaces combined? | `factors_iff` and `copair_eta` cover request restriction and tagged sum. `relabel_extend` checks extension and dispatch. With a typed renaming both requests and reply fibers have equivalences. `observes_hide_reply`, `observes_hide_refuse`, `observes_hide_loop` and `hide_staged` cover a state-indexed partial reply policy, including refusal and silent divergence. [Operator guide][operators] · [Header][operators-thms] · [Regression][operators-check] |
| Which SQLite source is being read? | The inventory pins SQLite 3.54.1, including the amalgamation digest and split source at `57520227c95396ce39ba6ecaac8d475b78dd3964`. The operation notes follow rowid lookup and rollback-journal insert/commit through VDBE, B-Tree, Pager and VFS, with instrumented source fixtures. [Version and interfaces][inventory] · [Operation paths][operations] |
| What does the admitted read prove? | `staged_eq_composed` compares full staged and composed outcomes. `composed_trace` validates the recorded exchanges with the supplied handler. `readOnly_cold_warm_lookup` proves the same lookup and poststates after one complete cold page read and a warm acquisition with zero exchanges. The check module covers found and absent keys, cold/warm traces and a truncated file. [Read case][read-case] · [Header][read-thms] · [Checks][read-check] |
| What does the open typed read expose? | `vfsTree_corresponds` witnesses the open VFS tree's complete trace along the supplied handler's replies. `vfsTree_readOnly_cold_warm` gives the typed cold/warm observations. `handledPager_returns_staged` hides the Pager request and returns the complete staged outcome, including file/cache poststates and exchanges. [Typed read guide][typed-read] · [Header][typed-read-thms] · [Checks][typed-read-check] |
| What does interpreting both read paths prove? | `Read.Adapter.interpretations_agree` gives the same staged outcome from the handled Pager and handled lower VFS paths, with the exact file, cache and exchange history. It validates that history and exhibits it in the open VFS tree. `lowered_observations_eq` equates the full open observation sets for staged lookup and the VM leaf continuation. Fixtures check cold and warm histories for present and absent keys. [Adapter guide][read-adapter] · [Header][read-adapter-thms] · [Checks][read-adapter-check] |
| What does the selected rollback-mode write prove? | After VM operand admission and a fresh-key leaf preflight, `run_follows_schedule` validates the completed calls, first error and handler poststate. `database_write_requires_journal` orders any database write attempt after a successful preimage write and journal sync. Under the packed-page and backing assumptions, `commit_success` reopens to the inserted row and all old rows, and `journal_sync_failure` retains the preimage and leaves the database unchanged on the selected fault. `run_observes` embeds the handler-selected trace and `no_ub` excludes the tree's explicit UB marker. [Write case][write-case] · [Header][write-thms] |

## Where the terms apply

- **May observation and refinement.** The observations record possible
  completed exchanges and terminal outcomes, silent divergence, and
  infinite exchange streams. Refinement is inclusion from implementation to
  specification. Both raw choice kinds are hidden and count as internal
  progress. Branching structure, choice indices, finite internal timing and
  root provenance are erased by observation. Bisimulation, must behavior
  and timing equivalence are outside these statements. [Interaction guide][interaction]
- **Guarded, handled and hidden.** Context-indexed requests and replies
  apply to the first-order guarded fragment. The Elgot fold has its own
  weak-tree source and lawful target assumptions. Higher-order effects,
  general handler adequacy and Elgot laws for the delayed choice model are
  outside this scope. Sequential hiding answers a request before
  observation or returns a designated refusal. SC projection filters an
  already generated history. [Guarded header][guarded-thms] · [Iteration header][elgot-thms] · [Operator guide][operators] · [Projection guide][sc-projection]
- **UB and ordinary errors.** A racing SC prefix is the raw trace through
  the attempted racing extension. The interaction UB marker denotes a
  completed run returning `none` at a chosen boundary, and saturation may
  extend that whole row. The correspondences here supply no translation
  from SC race prefixes to catastrophic rows. A modeled VFS error or
  rejected short read is an ordinary return. Handling the Pager and exposing
  the lower VFS use different observation points. [SC header][sc-thms] · [UB header][ub-thms] · [Typed read guide][typed-read] · [Write case][write-case]
- **SC, races and calls.** SC orders primitive actions. The race
  definitions operate on event positions, with mutex synchronization and,
  in the mixed profile, atomic reads-from edges on generated histories.
  The raw label tests can accept impossible histories before validation.
  The model has no scheduler fairness or starvation guarantee. Race freedom supplies no
  general atomicity or linearizability of compound calls, as the lost-update
  example illustrates. [SC and race guide][sc] · [Examples][sc-check]
- **SQLite admission.** The read starts at acquisition of a designated
  512-byte packed rowid leaf with an open handle. The Lean model rejects
  short reads, while the pinned C main-file path can pass a zero-filled
  buffer to page-format admission. The write starts after transaction setup
  with an admitted cursor, resident leaf and open journal in the canonical
  two-page model. In pinned C, journal opening precedes the dirty mark,
  and preimage recording precedes marking the page writable. The model
  starts with the journal open and represents the later cached leaf edit.
  Its selected sync acknowledgements express ordering.
  Whole SQL execution, C or native refinement, WAL, contention, durability
  and crash recovery are outside these claims. [Operation paths][operations] · [Read case][read-case] · [Write case][write-case]

## Review status

The linked source revisions are immutable because the component changes
are under review, with some based on other component branches. The map
covers the pinned statements and their stated premises. The component PRs
record publication and check status. [Inventory][pr-inventory] · [SC][pr-sc] · [Interaction][pr-interaction] · [Projection][pr-projection] · [Operators][pr-operators] · [Read][pr-read] · [Open typed read][pr-typed-read] · [Handled read adapter][pr-read-adapter] · [Institutions and Elgot][pr-institution] · [Write][pr-write]

[interaction]: https://github.com/hiloopai/silmaril-lean/blob/9c76bcfd3e7f9266327e065191b1d39ddb423f68/docs/projects/track-a-interaction.md
[interaction-thms]: https://github.com/hiloopai/silmaril-lean/blob/9c76bcfd3e7f9266327e065191b1d39ddb423f68/Silmaril/Semantics/TrackA/Interaction/Thms.lean
[interaction-check]: https://github.com/hiloopai/silmaril-lean/blob/9c76bcfd3e7f9266327e065191b1d39ddb423f68/Silmaril/Proofs/Semantics/TrackA/Interaction/Regression.lean
[guarded-thms]: https://github.com/hiloopai/silmaril-lean/blob/9c76bcfd3e7f9266327e065191b1d39ddb423f68/Silmaril/Semantics/TrackA/Interaction/Guarded/Thms.lean
[weak-thms]: https://github.com/hiloopai/silmaril-lean/blob/9c76bcfd3e7f9266327e065191b1d39ddb423f68/Silmaril/Semantics/TrackA/Interaction/WeakITree/Thms.lean
[ub-thms]: https://github.com/hiloopai/silmaril-lean/blob/9c76bcfd3e7f9266327e065191b1d39ddb423f68/Silmaril/Semantics/TrackA/Interaction/UB/Thms.lean
[institution]: https://github.com/hiloopai/silmaril-lean/blob/5e08c16a7b9d14127a9686f600039089fee36027/docs/projects/track-a-interaction-institution.md
[institution-thms]: https://github.com/hiloopai/silmaril-lean/blob/5e08c16a7b9d14127a9686f600039089fee36027/Silmaril/Logic/TrackA/Interaction/Thms.lean
[institution-check]: https://github.com/hiloopai/silmaril-lean/blob/5e08c16a7b9d14127a9686f600039089fee36027/Silmaril/Proofs/Logic/TrackA/Interaction/Regression.lean
[relabel-thms]: https://github.com/hiloopai/silmaril-lean/blob/5e08c16a7b9d14127a9686f600039089fee36027/Silmaril/Semantics/TrackA/Interaction/Relabel/Thms.lean
[elgot-thms]: https://github.com/hiloopai/silmaril-lean/blob/5e08c16a7b9d14127a9686f600039089fee36027/Silmaril/Semantics/TrackA/Interaction/Elgot/Thms.lean
[sc]: https://github.com/hiloopai/silmaril-lean/blob/b93f7a72e2ad4a244ffd17bb5e94858a2c73fc3b/docs/projects/track-a-concurrency.md
[sc-thms]: https://github.com/hiloopai/silmaril-lean/blob/b93f7a72e2ad4a244ffd17bb5e94858a2c73fc3b/Silmaril/Semantics/TrackA/Concurrency/Thms.lean
[sc-check]: https://github.com/hiloopai/silmaril-lean/blob/b93f7a72e2ad4a244ffd17bb5e94858a2c73fc3b/Silmaril/Proofs/Semantics/TrackA/Concurrency/Examples.lean
[sc-projection]: https://github.com/hiloopai/silmaril-lean/blob/99cd8a9f92531530e3bd865036946844c90fa69c/docs/projects/track-a-concurrency.md#interface-observations
[projection-thms]: https://github.com/hiloopai/silmaril-lean/blob/99cd8a9f92531530e3bd865036946844c90fa69c/Silmaril/Semantics/TrackA/Concurrency/Projection/Thms.lean
[projection-check]: https://github.com/hiloopai/silmaril-lean/blob/99cd8a9f92531530e3bd865036946844c90fa69c/Silmaril/Proofs/Semantics/TrackA/Concurrency/Projection/Examples.lean
[operators]: https://github.com/hiloopai/silmaril-lean/blob/d9cb51eb8351f6c9c50b0a947e3b533da072644a/docs/projects/track-a-interface.md
[operators-thms]: https://github.com/hiloopai/silmaril-lean/blob/d9cb51eb8351f6c9c50b0a947e3b533da072644a/Silmaril/Semantics/TrackA/Interface/Thms.lean
[operators-check]: https://github.com/hiloopai/silmaril-lean/blob/d9cb51eb8351f6c9c50b0a947e3b533da072644a/Silmaril/Proofs/Semantics/TrackA/Interface/Regression.lean
[inventory]: https://github.com/hiloopai/silmaril-lean/blob/c43ef4a85c5948119be11834f4feebce75dc4991/docs/projects/sqlite-track-a/header-inventory/README.md
[operations]: https://github.com/hiloopai/silmaril-lean/blob/c43ef4a85c5948119be11834f4feebce75dc4991/docs/projects/sqlite-track-a/header-inventory/operations.md
[read-case]: https://github.com/hiloopai/silmaril-lean/blob/852fe2dcb8628565856abe1074273abd96ce27ff/docs/projects/sqlite-track-a/read-case.md
[read-thms]: https://github.com/hiloopai/silmaril-lean/blob/852fe2dcb8628565856abe1074273abd96ce27ff/Silmaril/Machine/SQLite/TrackA/Read/Thms.lean
[read-check]: https://github.com/hiloopai/silmaril-lean/blob/852fe2dcb8628565856abe1074273abd96ce27ff/Silmaril/Machine/SQLite/TrackA/Read/Checks.lean
[typed-read]: https://github.com/hiloopai/silmaril-lean/blob/b71f7df50b00679ab5e3784ba694621d54731920/docs/projects/sqlite-track-a/read-interaction.md
[typed-read-thms]: https://github.com/hiloopai/silmaril-lean/blob/b71f7df50b00679ab5e3784ba694621d54731920/Silmaril/Machine/SQLite/TrackA/Read/Interaction/Thms.lean
[typed-read-check]: https://github.com/hiloopai/silmaril-lean/blob/b71f7df50b00679ab5e3784ba694621d54731920/Silmaril/Machine/SQLite/TrackA/Read/Interaction/Checks.lean
[read-adapter]: https://github.com/hiloopai/silmaril-lean/blob/43bb1542eea70e6199b1fd8e3af184cef5673d9c/docs/projects/sqlite-track-a/typed-read-adapter.md
[read-adapter-thms]: https://github.com/hiloopai/silmaril-lean/blob/43bb1542eea70e6199b1fd8e3af184cef5673d9c/Silmaril/Machine/SQLite/TrackA/Read/Adapter/Thms.lean
[read-adapter-check]: https://github.com/hiloopai/silmaril-lean/blob/43bb1542eea70e6199b1fd8e3af184cef5673d9c/Silmaril/Machine/SQLite/TrackA/Read/Adapter/Checks.lean
[write-case]: https://github.com/hiloopai/silmaril-lean/blob/814bed538f10118fb9b0810d3e78902c99395040/docs/projects/sqlite-track-a-write.md
[write-thms]: https://github.com/hiloopai/silmaril-lean/blob/814bed538f10118fb9b0810d3e78902c99395040/Silmaril/Machine/SqliteVfs/TrackA/Write/Thms.lean
[pr-inventory]: https://github.com/hiloopai/silmaril-lean/pull/3531
[pr-sc]: https://github.com/hiloopai/silmaril-lean/pull/3539
[pr-interaction]: https://github.com/hiloopai/silmaril-lean/pull/3543
[pr-projection]: https://github.com/hiloopai/silmaril-lean/pull/3559
[pr-operators]: https://github.com/hiloopai/silmaril-lean/pull/3564
[pr-read]: https://github.com/hiloopai/silmaril-lean/pull/3555
[pr-typed-read]: https://github.com/hiloopai/silmaril-lean/pull/3572
[pr-institution]: https://github.com/hiloopai/silmaril-lean/pull/3576
[pr-read-adapter]: https://github.com/hiloopai/silmaril-lean/pull/3583
[pr-write]: https://github.com/hiloopai/silmaril-lean/pull/3580
