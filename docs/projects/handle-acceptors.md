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
| Wasm modules, reader checkers | Wasm | `Silmaril.Wasm.Game.HandleAccept.{Defs,Thms}`, `…HandleAccept.Checkers.{Defs,Thms}` |

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
* *traps* (no response: nothing follows) versus *undefined behaviour* (`chaos`: the event and
  everything after accepts every tree, the top element).

Environments are always explicit: writer stores (`WState.store`), fixed environments
(`fix = some ρ`, `fixedLang … Envs`), reader environment sets (`readerLang … Envs`), parse
environments (`parseRel … Envs`).

## Coverage checklist

### 1. Writer acceptor API

| Item | Status | Where |
| --- | --- | --- |
| `symbol(string)->i32`, `sexp(list<i32>)->i32`, `accept(i32)` | done (abstract), see 7 for Wasm | `Handle.Writer`, `WEv.write/accept`; S-expression instance `Formats.SExp.Api` |
| successful handles arbitrary, never reused; interning allowed | done | `Fresh`, `Policy.intern`; persistence `Run.store_extends` |
| invalid accept: mandatory trap | done | `OnInvalid.trap`, `WStep.acceptTrap` (`dead` phase) |
| invalid accept: ignored, traps permitted as a foreign call | done | `OnInvalid.ignore` (a trace may end anywhere) |
| invalid accept: UB = all behaviour | done | `OnInvalid.ub`, `WStep.acceptChaos`/`chaos` |
| UB restricted to fixed `i32 → tree` environments agreeing with allocations | done | `fix = some ρ`, `Agrees`, `WStep.writeFixed/acceptFixed`, `fixedLang` |
| error-return accept variant | done | `WEv.acceptErr`, `writerLang_subset_eraseErr`, `writerLang_eraseErr_eq` (`ResultOblivious`) |
| relationships under explicit observations | done | `writerLang_mono` (`Policy.Le`), chain `writerLang_subset_fixedLang`, `fixedLang_subset`; strictness `Examples.trap_ne_ignore`, `fixed_lt_ub`, `fixed_trace_lt_ub` |
| failure sentinel `0` or `-1` | done | `Policy.sentinel`, `writerLang_sentinel_swap` (the two correspond by the handle swap `0 ↔ -1`, not by numeric identity) |
| acceptance with sentinel ≤ without, exact assumptions | done | `writerLang_noRet`, `writerLang_noRet_subset` (traces never receiving the sentinel); counterexample with two failures `Examples.sentinel_twice` |
| finite `i32` capacity, freshness vs aliases/interning | done | `successes_nodup`, `successes_length_le` (no interning: at most `\|{h ≠ sentinel}\|` successes) |
| consistent environments | done | stores only grow (`Run.store_extends`); fixed `ρ` must agree with every allocation |
| constructed set as accepted, downward closed | done | `WEv.acceptAll`, `writerLang_downClosed` (`Writer.ChildRel`) |
| `accept_all()` since start; `accept_all(bool)` batches since previous call | done | `WEv.acceptAll`, `WEv.acceptBatch`; batches are not downward closed: `Examples.batch_not_downClosed` |

### 2. Reader APIs

| Item | Status | Where |
| --- | --- | --- |
| `accept(i32)`, `tag`, `symbol`, `sexp(i32)->list<i32>`; `children` count, `child(i32,i32)` | done (abstract signature), S-expression queries in `Formats.SExp.Api` | `Reader`, `REv` |
| fixed environment `i32 → tree` or `option tree` | done | `Env` (partial), `Env.ofTotal` |
| handles chosen by the module, arbitrary export sequences | done | traces are arbitrary event lists, not a single `check(h)` |
| invalid reads: arbitrary data, trap, typed error, default, UB | done | `OnBadRead.{arbitrary,trap,dflt,ub}`, typed error = `dflt` + `ErrorDisjoint` (`error_iff_invalid`) |
| arbitrary data ≠ UB | done | `Examples.arbitrary_ne_ub`, `Examples.arbitrary_uncertified` |
| relations | done | `readerLang_mono` (`OnBadRead.Le`), `trap_reads_correct`, `readerLang_trap_subset` (certified acceptance) |
| more atoms: `blob(bytes)`, `string`, `word(i64)`, keywords | see 3 | `Formats.SExp.Family` |

### 3. First-class family APIs

| Item | Status | Where |
| --- | --- | --- |
| symbols, byte trees, word trees, symbols+strings, symbols+bytes, symbols+strings+bytes, symbols+strings+keywords, symbols+strings+keywords+bytes | done (tree types and writer/reader signatures) | `Formats.SExp.Family.Defs`: `SymbolSExp`, `ByteSExp`, `WordSExp`, `SymStrSExp`, …, `Atom ks`, `AtomKind`; one parameterized writer `Api.sexpW α` and reader `Api.sexpR α H` instantiated per family (no per-family code duplication) |
| Rivest canonical vs display hints | done | `RivestSExp` (hint-free, existing), `HintedSExp` with `HintedSExp.toSpki` into RFC 9804 `Spki.Sexp`, `HintedSExp.toSpki_injective`; the docstring explains that canonical encodings carry hints |
| Wasm import decoders for string/byte-carrying imports (`symbol(string)`, `blob`, `sexp(list<i32>)`) | **planned** | need memory-observing sessions (`Wasm.Game.Accept.Callout.mem`); instance plays carry no memory |

### 4. Generic branch/leaves and tagged ASTs

| Item | Status | Where |
| --- | --- | --- |
| generic `branch(children)` + designated leaves `tag(args)` | done | `AstSig`, `AST S := TExpr1 (Σ t, S.Arg t)` (reuses `TExpr`), `AST.WellArity`, `Api.astW` |
| typed heterogeneous WIT payloads | done (payload universe) | `PTy` (`bool`, `s32`, `u32`, `s64`, `u64`, `string`, `list<u8>`, `list<T>`), `PTy.Vals`, `WitSig.toAstSig`; relating `PTy` to `Wasm.Component…WIT.ValType` is **planned** |
| variadic `tag(args…, children: list<i32>)`, fixed arity `tag(args…, c₁…cₙ)`, mixed arities | done (semantics) | `Arity.fixed`/`star`, `Arity.Admits`, one writer `astW` for both import shapes; Wasm decoders **planned** |
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
| patterns over SExpr/SExpr2/AST with acceptors as an extra atom | done (definitions; laws for `Pat`) | `Pat`, `Pat2`, `PatAST` and their `lang`; `Pat.lang_ground`, `Pat.lang_mono`; laws for `Pat2`/`PatAST` **planned** |
| AST→sexp `(tag arg₁…argₙ child₁…childₙ)`, per-tag layouts, soundness assumptions | done | `AST.encode`, `AST.encodeWith`, `AST.encode_injective` (`ArgLenFixed`), `encode_image_injective`; counterexample `Formats.Examples.enc_collides` |

### 7. Executable Wasm checkers

| Item | Status | Where |
| --- | --- | --- |
| module languages grounded in core Wasm | done (definitions) | `Wasm.Game.HandleAccept`: `playEvents`, `handleTraces` over `(instOf m).strategy P s` plays (every profile, every environment, any export sequence), `moduleConsLang` |
| link from Hoare-logic specifications to language soundness | done | `readerLang_subset_of_AG` (generic), `consLang_sound_of_gameSat`, `consLang_sound_of_forall` via `GameLink.strategy_sound` |
| proper lists in `SExp2`, `[i64]` word lists, sorted word lists, subset theorem | partial | modules `properCheck`, `wordsCheck`, `sortedCheck` (validated and instantiated by `decide +kernel`); `sortedL_subset_wordsL`, `wordsL_subset_properL`; soundness **conditional** on the frozen obligations `Task.properCheckSat`, `Task.wordsCheckSat`, `Task.sortedCheckSat` (`*_sound_of`), whose Hoare-logic proofs are **not done** |
| signed `i32` handles vs `i64` payloads, sorting | done (stated) | `Checkers.Defs` docstring; `sortedL` uses signed `BitVec.sle` (`i64.le_s`) |
| n-ary `[i32]` words through `count`/`child`, binary (`Tree2`) checkers, writer-side Wasm modules, non-vacuity runs | **planned** | |

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
| c. chunks, `done() -> (used, tree)`, cursor, failure advances, unconsumed suffix, bounds | done | `PEv.feed/finish`, `Returns`, `run_cursor`, `parseRel_slice`, `onOverrun`, `usedOfI32`/`usedOfI32_lt`, `Examples.chunk_example` |
| repeated `done`, sessions, `reset` | done | `doneClears`, `PEv.reset`, `Examples.done_twice` |
| projections, membership, monotonicity, unions, non-preservation of intersections | done | `inputLang`, `treeLang`, `inputLang_union`, `inputLang_inter_subset`, `parseRel_mono`, `parseRel_union`, `Examples.projection_inter_strict` |
| trees resolved in consistent environments; mixed APIs with parsing; Wasm tie-ins | partial | environments are explicit (`parseRel … Envs`); a combined writer+parse host and Wasm decoders are **planned** |

### Cautions

| Caution | Where |
| --- | --- |
| explicitly quantified environments | `Envs` parameters, `fix`, `langOver` |
| restriction vs nondeterminism vs trap vs UB top | `Sim`, `Phase.dead`, `Phase.chaos` |
| well-founded fixed environments, no silent cycles | `NodeEnv`, `UnfoldN`/`Unfold`, `not_unfold_of_cycle`, `realize_realizes`, `Examples.cycle_unfolds_to_nothing` |
| sentinel inclusion via observations/renamings, allocation failure | `writerLang_rename`, `writerLang_sentinel_swap`, `writerLang_noRet_subset`, `sentinel_twice` |
| intersection is not preserved by projection or trace languages | `Host.lang_inter_subset`, `inputLang_inter_subset`, `Examples.inter_strict`, `projection_inter_strict` |

## Modelling choices to review

* A mandatory trap on `accept` makes the environment `dead` for the rest of the session. In a
  Wasm instance a trap aborts only the current export call; that reading lies between `trap`
  and `ignore` here.
* Allocation failure with a sentinel is always allowed (capacity is the environment's); without
  a sentinel a failing allocation traps.
* `SExp2.toSExp?` is defined by classical choice (the unique preimage); a computable decoder is
  not provided.
* The Wasm reading uses instance plays (`Verify.instOf`, every profile), which carry argument
  values and results but not memory.

## Remaining obligations

1. Prove `Task.properCheckSat`, `Task.wordsCheckSat`, `Task.sortedCheckSat`: `GameSat` for the
   three checker modules (loop invariants relating the current handle to `ρ`, in the style of
   `Silmaril.Proofs.Wasm.Spec.Attest.Safe`).
2. Non-vacuity of the checker languages by a replayed play (`Silmaril.Wasm.Resource.Replay`).
3. Wasm decoders for writer APIs, for `count`/`child` n-ary readers, binary-tree readers,
   fixed-arity AST imports, and the parsing exports; memory-carrying imports through
   `Silmaril.Wasm.Game.Accept` callouts.
4. `PTy` ↔ WIT value types; laws for `Pat2`/`PatAST`; a combined writer + parsing host.
5. The sentinel reinterpretation theorem for a single failure (only the no-failure inclusion and
   the two-failure counterexample are proved).

## Checking

```
lake build --wfail Silmaril.Semantics.Accept.Handle.Examples Silmaril.Semantics.Accept.Parse.Examples \
  Silmaril.Formats.SExp.Api.Thms Silmaril.Formats.SExp.Pattern.Examples \
  Silmaril.Formats.SExp.Family.Thms Silmaril.Wasm.Game.HandleAccept.Checkers.Thms
scripts/check-layout.sh
```

`make check` builds everything; a library-only build does not run the executable tests.
