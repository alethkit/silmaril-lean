# Handle-based tree acceptors: design and coverage

This development answers: *what trees does a module accept* when it talks to its environment
through **handles** (`i32` values the environment interprets as trees), rather than through
bytes in memory? It covers writer (constructor) APIs, reader (inspection) APIs, their
combination, parsing sessions, the tree families they produce, abstract acceptors over those
families, and the link to core Wasm modules.

The checklist below maps every item of the original request (1–9) and the additional cautions
to files, theorem names and tests. Status: **done** (in this branch, built with `--wfail`),
**partial** (what exists and what does not), **planned** (nothing yet). Nothing marked planned
is claimed anywhere in the Lean sources.

## Layers

| Layer | Region | Modules |
| --- | --- | --- |
| Host models (generic) | Semantics | `Silmaril.Semantics.Accept.Host.{Defs,Thms}` |
| Handle APIs: writers, readers, combined, node environments | Semantics | `Silmaril.Semantics.Accept.Handle.{Defs,Thms,Examples}` |
| Parsing sessions | Semantics | `Silmaril.Semantics.Accept.Parse.{Defs,Thms,Examples}` |
| Tree families, AST signatures, APIs, patterns | Formats | `Silmaril.Formats.SExp.Family`, `…SExp.Api`, `…SExp.Pattern` |
| Wasm modules, decoders, checkers | Wasm | `Silmaril.Wasm.Game.HandleAccept.{Defs,Thms}`, `…HandleAccept.Checkers.{Defs,Thms}` |

Proofs longer than a few lines are under `Silmaril/Proofs/<Region>/…` and reached only through
the `Thms` headers.

### The common semantics

A module's behaviour is a set of **event traces**; an event is a call with the answer the
module observed (`Host`). A host model says which answers the environment may give and what a
call makes the module accept; `Host.lang h T` is the union over traces. Three kinds of
environment behaviour are kept apart everywhere:

* *nondeterministic answers* (several responses: interning or not, allocation failure,
  arbitrary data for invalid reads);
* *restriction* of the environment (fewer responses; `Sim` gives inclusion of languages; fixed
  environments `fixedLang`, environment sets `Envs`);
* *traps* versus *undefined behaviour* (`chaos`: the event and everything after accepts every
  tree, the top element). A trap is **call-local** by default, as in Wasm: it aborts the current
  export call (phase `aborted`), the instance and its store persist, and the next export call
  (`enter`, decoded from the export-call move of a play) resumes; a session abort (phase `dead`,
  nothing follows) is an optional stricter policy.

Environments are always explicit: writer stores (`WState.store`), fixed environments
(`fix = some ρ`, `fixedLang … Envs`), reader environment sets (`readerLang … Envs`), parse
environments (`parseRel … Envs`).

## Coverage checklist

### 1. Writer acceptor API

| Item | Status | Where |
| --- | --- | --- |
| `symbol(string)->i32`, `sexp(list<i32>)->i32`, `accept(i32)` | done (abstract), see 7 for Wasm | `Handle.Writer`, `WEv.write/accept`; S-expression instance `Formats.SExp.Api` |
| successful handles arbitrary, never reused; interning allowed | done | `Fresh`, `Policy.intern`; persistence `Run.store_extends`, `write_persists` |
| invalid accept: mandatory trap (Wasm-facing, call-local) | done | `OnInvalid.callTrap` (the default), `WStep.acceptCallTrap` (`aborted` phase until the next export call `WEv.enter`, `WStep.resume`; `WStep.aborted_inv`: only `enter` follows, store and batch unchanged). Effects before the trap persist: `write_persists`, `Examples.persist_seven` (write `7` at `1`, invalid accept, `enter`, `accept 1` accepts `7`) |
| invalid accept: session abort (optional, stricter) | done | `OnInvalid.sessionTrap`, `WStep.acceptSessionTrap` (`dead` phase: nothing follows, not even an export call, `WStep.not_dead`); within one export call it agrees with `callTrap` (`writerLang_callTrap_eq_sessionTrap`, traces with no `enter` after their first event) |
| invalid accept: ignored, traps permitted as a foreign call | done | `OnInvalid.ignore` (a trace may end anywhere) |
| invalid accept: UB = all behaviour | done | `OnInvalid.ub`, `WStep.acceptChaos`/`chaos` |
| UB restricted to fixed `i32 → tree` environments agreeing with allocations | done | `fix = some ρ`, `Agrees`, `WStep.writeFixed/acceptFixed`, `fixedLang` |
| error-return accept variant | done | `WEv.acceptErr`, `writerLang_subset_eraseErr`, `writerLang_eraseErr_eq` (`ResultOblivious`) |
| relationships under explicit observations | done | `writerLang_mono` (`Policy.Le`, ranks `sessionTrap ≤ callTrap ≤ ignore ≤ ub`), `writerLang_onAccept_mono`, chain `writerLang_sessionTrap_subset_callTrap`, `writerLang_callTrap_subset_ignore`, `writerLang_ignore_subset_ub`; fixed environments `writerLang_subset_fixedLang`, `fixedLang_subset`; strictness `Examples.callTrap_ne_sessionTrap` (invalid accept in call 1, valid in call 2: `[accept 0, enter, write (lit 7) → 1, accept 1]`), `Examples.callTrap_ne_ignore` and `sessionTrap_ne_ignore` (invalid then valid in the same call), `fixed_lt_ub`, `fixed_trace_lt_ub` |
| failure sentinel `0` or `-1` | done | `Policy.sentinel`, `writerLang_sentinel_swap` (the two correspond by the handle swap `0 ↔ -1`, not by numeric identity) |
| acceptance with sentinel ≤ without, exact assumptions | done | The anticipated raw inclusion `writerLang (sentinel s) T ⊆ writerLang (no sentinel) T` is **false** (`Examples.sentinel_twice`: two failures at handle `0` for different trees cannot be read as allocations, since a sentinel-free environment never returns one handle for two trees). What holds: (1) restriction: traces that never receive the sentinel (`writerLang_noRet`, `writerLang_noRet_subset`); (2) reinterpretation: with trapping invalid writes, a trace with at most one failure whose result is never used again (`OneUnusedFailure`) accepts no more than without a sentinel, reading the failure as a successful allocation of `s` (`accepts_subset_of_oneFailure`, `writerLang_subset_of_oneFailure`, `Examples.ten_one_failure`); (3) `0` vs `-1` correspond by the handle swap (`writerLang_sentinel_swap`) |
| finite `i32` capacity, freshness vs aliases/interning | done | `successes_nodup`, `successes_length_le` (no interning: at most `\|{h ≠ sentinel}\|` successes) |
| consistent environments | done | stores only grow (`Run.store_extends`); fixed `ρ` must agree with every allocation |
| constructed set as accepted, downward closed | done | `WEv.acceptAll`, `writerLang_downClosed` (`Writer.ChildRel`) |
| `accept_all()` since start; `accept_all(bool)` batches since previous call | done | `WEv.acceptAll`, `WEv.acceptBatch`; batches are not downward closed: `Examples.batch_not_downClosed` |

### 2. Reader APIs

| Item | Status | Where |
| --- | --- | --- |
| `accept(i32)`, `tag`, `symbol`, `sexp(i32)->list<i32>`; `children` count, `child(i32,i32)` | done (abstract signature), S-expression queries in `Formats.SExp.Api` | `Reader`, `REv` |
| fixed environment `i32 → tree` or `option tree` | done | `Env` (partial), `Env.ofTotal` |
| handles chosen by the module, arbitrary export sequences | done | traces are arbitrary event lists with export-call boundaries `REv.enter`, not a single `check(h)` |
| invalid accept | done | `OnInvalid` as for writers: `RStep.acceptCallTrap` (`aborted` until `enter`), `acceptSessionTrap` (`dead`), `acceptIgnore`, `acceptChaos`; chain `readerLang_sessionTrap_subset_callTrap`, `readerLang_callTrap_subset_ignore`, `readerLang_ignore_subset_ub`; `readerLang_callTrap_eq_sessionTrap` within one export call |
| invalid reads: arbitrary data, trap, typed error, default, UB | done | `OnBadRead.{arbitrary,trap,dflt,ub}`, typed error = `dflt` + `ErrorDisjoint` (`error_iff_invalid`) |
| arbitrary data ≠ UB | done | `Examples.arbitrary_ne_ub`, `Examples.arbitrary_uncertified` |
| relations | done | `readerLang_mono` (`OnBadRead.Le`, accept ranks), `trap_reads_correct`, `readerLang_trap_subset` (certified acceptance, every accept policy but `ub`; `readerLang_trap_subset_callTrap` for the call-local trap, reads stay correct across export calls) |
| more atoms: `blob(bytes)`, `string`, `word(i64)`, keywords | see 3 | `Formats.SExp.Family` |

### 3. First-class family APIs

| Item | Status | Where |
| --- | --- | --- |
| symbols, byte trees, word trees, symbols+strings, symbols+bytes, symbols+strings+bytes, symbols+strings+keywords, symbols+strings+keywords+bytes | done (tree types and writer/reader signatures) | `Formats.SExp.Family.Defs`: `SymbolSExp`, `ByteSExp`, `WordSExp`, `SymStrSExp`, …, `Atom ks`, `AtomKind`; one parameterized writer `Api.sexpW α` and reader `Api.sexpR α H` instantiated per family (no per-family code duplication) |
| Rivest canonical vs display hints | done | `RivestSExp` (hint-free, existing), `HintedSExp` with `HintedSExp.toSpki` into RFC 9804 `Spki.Sexp`, `HintedSExp.toSpki_injective`; the docstring explains that canonical encodings carry hints |
| Wasm import decoders for string/byte-carrying imports (`symbol(string)`, `blob`, `sexp(list<i32>)`) | done (decoders, structural bound) | `Wasm.Game.HandleAccept.Memory`: `memWrite`/`memAccept` roles over memory-observing traced sessions (`memTraces` on `tagTraces`), `memWriterLang` over `SymStrBytesSExp`; `inp_of_tsession`, `memWriterLang_subset_atoms`; 12 kernel-checked decodings in `Memory.Examples`. An assume/guarantee bridge for memory-carrying traces is **not done** |

### 4. Generic branch/leaves and tagged ASTs

| Item | Status | Where |
| --- | --- | --- |
| generic `branch(children)` + designated leaves `tag(args)` | done | `AstSig`, `AST S := TExpr1 (Σ t, S.Arg t)` (reuses `TExpr`), `AST.WellArity`, `Api.astW` |
| typed heterogeneous WIT payloads | done | `PTy`, `PTy.Vals`, `WitSig.toAstSig`; `Wasm.Game.HandleAccept.Wit`: `toWit : PTy → WIT.ValType`, `toWit_simple`, `toWit_injective`, `valEquiv E t : PTy.Val t ≃ (toWit t).Interp E`, `valsEquiv` |
| variadic `tag(args…, children: list<i32>)`, fixed arity `tag(args…, c₁…cₙ)`, mixed arities | done | one writer `astW`; Wasm fixed-arity decoders `Wasm.Game.HandleAccept.Ast` (`moduleAstWLang`, `moduleAstWLang_wellArity` for every module, `astWLang_sound_of_gameSat`); AST reader `moduleAstLang`, `astLang_sound_of_gameSat`; variadic imports carry a memory list (see `Memory`) |
| simple APIs are special cases | done | `Api.sexpW_hom` (writer homomorphism), `sexpLang_eq_astLang`, generic `writerLang_hom`/`writerLang_hom_subset` |
| SExpr ≅ single payload-free variadic branch tag + atom leaves | done | `sexpSig`, `SExp.equivAST : SExp α ≃ {x // WellArity x}`; atoms are not unlabelled internal nodes: `leaf_children_not_wellArity` |

### 5. Cons API and n-ary vs dotted

| Item | Status | Where |
| --- | --- | --- |
| `nil()`, `symbol`/atoms, `cons(i32,i32)`; cons without `nil` | done | `Api.consW` (`SExp2`), `Api.pairW` (`Tree2`), `consW_childRel` |
| n-ary vs `SExp2` (improper lists), properness, roundtrips | done | existing `SExp.toSExp2`, `toSExp2_injective`, `proper_iff_exists`; new `SExp2.toSExp?` with `toSExp?_toSExp2`, `toSExp2_of_toSExp?`, `isProper_iff_toSExp?` |
| tagged AST embeddings | done | existing `TExpr.equivSExp`, `TExpr1.equivTree2`, `TExpr1.equivSExp2`; new `SExp.equivAST` |

### 6. Abstract acceptors

| Item | Status | Where |
| --- | --- | --- |
| union/intersection, images/preimages (incl. `SExp → SExp2`) | done | languages are `Set`s; `Set.image SExp.toSExp2` etc.; homomorphism images `writerLang_hom` |
| combinators `(a₁ a₂)`, `(a₁ … aₙ)`, `star` | done | `pair`, `tuple`, `star`; `mem_pair`, `tuple_inter`, `pair_inter_left`, `pair_union_left`, `tuple_subset_star` |
| patterns over SExpr/SExpr2/AST with acceptors as an extra atom | done | `Pat`, `Pat2`, `PatAST` and their `lang`; `Pat.lang_ground`, `Pat.lang_mono`, `Pat2.lang_ground`, `Pat2.lang_mono`, `Pat2.lang_ofList`, `PatAST.lang_ground`, `PatAST.lang_mono`; `Pat.toPat2` with `Pat.toSExp2_image_lang` (image of a proper pattern's language along `SExp → SExp2`) |
| AST→sexp `(tag arg₁…argₙ child₁…childₙ)`, per-tag layouts, soundness assumptions | done | `AST.encode`, `AST.encodeWith`, `AST.encode_injective` (`ArgLenFixed`), `encode_image_injective`; counterexample `Formats.Examples.enc_collides` |

### 7. Executable Wasm checkers

| Item | Status | Where |
| --- | --- | --- |
| module languages grounded in core Wasm | done (definitions) | `Wasm.Game.HandleAccept`: `playEvents enter decAsk decAns`, `handleTraces` over `(instOf m).strategy P s` plays (every profile, every environment, any export sequence); export-call moves `.inr (.ask _)` decode to `enter` (`some .enter` in every module language: `moduleConsLang`, `moduleSExpLang`, `moduleAstLang`, `moduleTree2Lang`, `Writers.moduleTraces`; `Memory.memTraces` reads `Tag.enter` likewise), so module languages see call boundaries and a trapped call is followed by further export calls on the same store |
| link from Hoare-logic specifications to language soundness | done | `readerLang_subset_of_AG` (generic, every `oa ≠ .ub`), `consLang_sound_of_gameSat`, `consLang_sound_callTrap`, `consLang_sound_of_forall` via `GameLink.strategy_sound`; writers `fixedLang_subset_of_AG`, `writerLang_subset_of_AG` |
| proper lists in `SExp2`, `[i64]` word lists, sorted word lists, subset theorem | done (soundness) | modules `properCheck`, `wordsCheck`, `sortedCheck` (validated by `decide +kernel`); `properCheck_sat`, `wordsCheck_sat`, `sortedCheck_sat` (`GameSat` with store invariant `consInv`, every profile, every environment `ρ`); unconditional `properCheck_sound`, `wordsCheck_sound`, `sortedCheck_sound` (`moduleConsLang P m consIx .trap oa Envs ⊆ L` for every `Envs` and every accept policy `oa ≠ .ub`, in particular the Wasm-facing `callTrap`). `properL` is **spine** properness (`SpineProperList`: nil-terminated `cdr` spine, any elements), which is what `properCheck` checks; recursive properness `recProperL` is strictly smaller (`recProperL_ssubset_properL`, with `dottedElem_mem_properL`/`dottedElem_not_mem_recProperL`); `sortedL_subset_wordsL`, `wordsL_subset_properL` |
| non-vacuity of the checkers | done | `Checkers.Examples`: replayed instance plays (`Silmaril.Wasm.Resource.Replay`, `replayExport_play`) decoded into reader runs (`mem_consLang_of_replay`; a replay starts with its export call, decoded as `enter`, which the Boolean checks pass), under the call-local trap: `properCheck_accepts_12`, `wordsCheck_accepts_12`, `sortedCheck_accepts_12` (`ofAtoms [1, 2]`), `wordsCheck_accepts_21`, `properCheck_accepts_dottedElem`, for every profile admitting the deterministic interpreter's steps (`hP`) and every specification profile (`_spec`); negative: `sortedCheck_rejects_21`, `wordsCheck_rejects_dottedElem`, `properCheck_rejects_atom`. So `sortedL ⊊ wordsL ⊊ properL` is witnessed by the modules |
| signed `i32` handles vs `i64` payloads, sorting | done (stated) | `Checkers.Defs` docstring; `sortedL` uses signed `BitVec.sle` (`i64.le_s`) |
| other styles in Wasm (proved examples) | done | shared rules `Proofs/Wasm/Game/HandleAccept/Checkers/Generic.lean`. N-ary reader (`count`/`child`): `pairCheck_sound`, `wordsNCheck_sound` (`SExp.ofAtoms ws`), `sortedNCheck_sound`, `sortedNL_subset_wordsNL`. AST reader: `addCheck_sound` (`add(num a, num b)`). Parsing export: `nzParse_sound`/`nzParse_input` (one-shot inputs are single nonzero words; the tree is unconstrained because the export spec cannot constrain its imports). Binary trees (`Tree2`, cons without nil): writer/reader decoders, `combCheck_sound` (right combs of words). Writer: `twoWords_sound`, `twoWords_fixed_sound` (accepts only `(x x+1)`), for policies without a sentinel (the module does not test for failures). Structural bounds for every module: `moduleConsWLang_subset_atoms2`, `moduleSxWLang_subset_arities`, `moduleAstWLang_wellArity`, `moduleParseRel_input_oneShot`, `memWriterLang_subset_atoms` |
| non-vacuity of the other styles | done | generic replay decoding `Proofs/Wasm/Game/HandleAccept/Replay.lean` (`mem_readerLang_of_replay`, `mem_writerLang_of_replay`); `pairCheck_accepts_12`, `wordsNCheck_accepts_12`, `sortedNCheck_accepts_12`, `wordsNCheck_accepts_21`, `sortedNCheck_rejects_21`; `addCheck_accepts_12`; `combCheck_accepts_123`; `twoWords_accepts_0`, `twoWords_accepts_5` (fresh-handle host); `nzParse_relates_7` (needs `replayExportR`, which also records the export's answer). All for profiles admitting the deterministic interpreter's steps (`hP`) and every specification profile (`_spec`) |

### 8. Combined writer + reader

| Item | Status | Where |
| --- | --- | --- |
| successful writes agree with any future read; persistent immutable meanings; interning | done | `CEv`, `combined`, `combined_cut`, `combined_write`, `combined_read`, `combined_write_read`, `Reader.Mono.persist`; monotone readers `sexpR_mono`, `consR_mono`, `astR_mono` |
| all reader invalidity and writer failure policies | done | `CStep` reuses `WStep` and `answers` (every `OnBadRead`) |

### 9. Parsing variants

| Item | Status | Where |
| --- | --- | --- |
| a. `parse(data) -> i32`, sentinel failure | done | `PEv.parse`, `resolve`, `oneShotRel` |
| b. `append(data)`, `done() -> i32` | done | `PEv.append/done`, `parseRel_done`, `pending`, `doneClears` |
| c. chunks, `done() -> (used, tree)`, cursor, failure advances, unconsumed suffix, bounds | done | `PEv.feed/finish`, `Returns`, `run_cursor`, `parseRel_slice` (for the session-abort overrun policy `onOverrun = .sessionTrap`), `onOverrun`, `usedOfI32`/`usedOfI32_lt`, `Examples.chunk_example` |
| invalid returned handle, overrun: traps | done | every parsing event is itself an export call ending with its returned handle, so a call-local trap (`callTrap`, the default) is that call relating nothing while the session continues; it coincides with `ignore` (`PStep.retBadIgnore`, `PStep.overrunIgnore`). `sessionTrap` aborts the session (`PStep.retBadSessionTrap`, `dead`; an overrun has no answer) |
| repeated `done`, sessions, `reset` | done | `doneClears`, `PEv.reset`, `Examples.done_twice` |
| projections, membership, monotonicity, unions, non-preservation of intersections | done | `inputLang`, `treeLang`, `inputLang_union`, `inputLang_inter_subset`, `parseRel_mono`, `parseRel_union`, `Examples.projection_inter_strict` |
| trees resolved in consistent environments; mixed APIs with parsing; Wasm tie-ins | partial | environments are explicit (`parseRel … Envs`); export decoders `Wasm.Game.HandleAccept.Parse` (`parseDec`, `moduleParseRel`; trapped export calls are not events); a combined writer+parse host is **not done** |

### Cautions

| Caution | Where |
| --- | --- |
| explicitly quantified environments | `Envs` parameters, `fix`, `langOver` |
| restriction vs nondeterminism vs trap vs UB top | `Sim`, `Phase.dead`, `Phase.chaos` |
| well-founded fixed environments, no silent cycles | `NodeEnv`, `UnfoldN`/`Unfold`, `not_unfold_of_cycle`, `realize_realizes`, `Examples.cycle_unfolds_to_nothing` |
| sentinel inclusion via observations/renamings, allocation failure | `writerLang_rename`, `writerLang_sentinel_swap`, `writerLang_noRet_subset`, `sentinel_twice` |
| intersection is not preserved by projection or trace languages | `Host.lang_inter_subset`, `inputLang_inter_subset`, `Examples.inter_strict`, `projection_inter_strict` |

## Modelling choices to review

* **Traps are call-local.** The Wasm-facing mandatory trap on an invalid `accept` is
  `OnInvalid.callTrap` (the default): as in Wasm, a trap aborts only the current export
  invocation, while the instance and its store persist (the game strategy
  `ScalarInstance.strategy` keeps the store across export calls) and the environment may make
  arbitrary further export calls. The environment moves to `aborted`; only the next export call
  (`enter`) may follow and resumes `live` with the store unchanged (`WStep.aborted_inv`).
  Effects before the trap are not rolled back: successful writes stay allocated
  (`write_persists`, `Run.store_extends`, `Examples.persist_seven`).
* Aborting the whole session (`OnInvalid.sessionTrap`, phase `dead`) is an optional stricter
  policy. Ranks `sessionTrap ≤ callTrap ≤ ignore ≤ ub` order the languages
  (`writerLang_sessionTrap_subset_callTrap`, `writerLang_callTrap_subset_ignore`,
  `writerLang_ignore_subset_ub` and the reader analogues), both inclusions around `callTrap` are
  strict (`Examples.callTrap_ne_sessionTrap`, `Examples.callTrap_ne_ignore`), and within one
  export call the two traps agree (`writerLang_callTrap_eq_sessionTrap`,
  `readerLang_callTrap_eq_sessionTrap`). Reader soundness (`readerLang_trap_subset`, the
  checker theorems `*_sound`) holds for every accept policy but `ub`.
* Parsing exports are themselves the export calls: a trapped `parse`/`done` relates nothing and
  the session continues (`callTrap` coincides with `ignore` there); the cursor theorems assume
  the session-abort overrun policy.
* Allocation failure with a sentinel is always allowed (capacity is the environment's); without
  a sentinel a failing allocation traps.
* `SExp2.toSExp?` is defined by classical choice (the unique preimage); a computable decoder is
  not provided.
* The Wasm reading uses instance plays (`Verify.instOf`, every profile), which carry argument
  values and results but not memory.

## Remaining obligations

* No checker for recursive properness (`recProperL`).
* No assume/guarantee bridge for memory-carrying traced sessions (only decoders and the
  structural bound); chunk lists in memory for parsing; an `items(h) -> list<i32>` reader.
* `twoWords` with a sentinel; a combined writer + parsing host.

## Checking

```
lake build --wfail Silmaril.Semantics.Accept.Handle.Examples Silmaril.Semantics.Accept.Parse.Examples \
  Silmaril.Formats.SExp.Api.Thms Silmaril.Formats.SExp.Pattern.Examples \
  Silmaril.Formats.SExp.Family.Thms Silmaril.Wasm.Game.HandleAccept.Checkers.Thms
scripts/check-layout.sh
```

`make check` builds everything; a library-only build does not run the executable tests.
