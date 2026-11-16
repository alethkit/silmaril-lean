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
| Wasm modules | Wasm | `Silmaril.Wasm.Game.HandleAccept` |

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

### 3–6, 7, 8, 9

| Item | Status | Where |
| --- | --- | --- |
| 3. first-class family APIs (symbols, bytes, words, symbols+strings, …, Rivest) | see `Formats` section below | |
| 4. generic branch/leaves, tagged AST with WIT payloads, fixed/variadic/mixed arity, SExpr correspondences | see below | |
| 5. cons API, `SExp` vs `SExp2`, properness, roundtrips | see below | |
| 6. abstract acceptors, images/preimages, combinators, patterns, AST→sexp encodings | see below | |
| 7. executable Wasm checkers | see below | |
| 8. combined writer+reader consistency | done | `CEv`, `combined`, `combined_cut`, `combined_write`, `combined_read`, `combined_write_read`, `Reader.Mono.persist` |
| 9. parsing variants a/b/c, projections, union/intersection, cursor | done (abstract) | `Parse.PEv`, `parseRel`, `inputLang`/`treeLang`, `parseRel_slice`, `parseRel_done`, `run_cursor`, `usedOfI32_lt`, `Examples.projection_inter_strict`, `chunk_example`, `done_twice` |

### Cautions

| Caution | Where |
| --- | --- |
| explicitly quantified environments | `Envs` parameters, `fix`, `langOver` |
| restriction vs nondeterminism vs trap vs UB top | `Sim`, `Phase.dead`, `Phase.chaos` |
| well-founded fixed environments, no silent cycles | `NodeEnv`, `UnfoldN`/`Unfold`, `not_unfold_of_cycle`, `realize_realizes`, `Examples.cycle_unfolds_to_nothing` |
| sentinel inclusion via observations/renamings, allocation failure | `writerLang_rename`, `writerLang_sentinel_swap`, `writerLang_noRet_subset`, `sentinel_twice` |
| intersection is not preserved by projection or trace languages | `Host.lang_inter_subset`, `inputLang_inter_subset`, `Examples.inter_strict`, `projection_inter_strict` |

## Checking

```
lake build --wfail Silmaril.Semantics.Accept.Host.Thms Silmaril.Semantics.Accept.Handle.Examples \
  Silmaril.Semantics.Accept.Parse.Examples
scripts/check-layout.sh
```

`make check` builds everything; a library-only build does not run the executable tests.
