# Typed SIMPLE to PEG

This milestone formalizes the loop-free part of Figures 15 and 17 and the
successful-return direction of Theorem 2 in Tate, Stepp, Tatlock and Lerner’s
*Equality Saturation: A New Approach to Optimization*. The source is
arXiv:1012.1802v3, PDF SHA-256
`5bb3630c9a2a4766c5614b19148e865ee0797c693607b2cdd700b27c38df0b94`.
[Paper, §6](https://arxiv.org/pdf/1012.1802v3#page=29)

| Paper rule | Lean coverage |
| --- | --- |
| Trans-Var, Trans-Op | Typed slot lookup and strict primitive application, including nullary primitives |
| Trans-Asgn, Trans-Sub | Bind a fresh slot and project the live context. A projection can also rename or duplicate positional slots |
| Trans-Seq | Feed the first statement’s node context into the second |
| Trans-If | Translate both arms from the entry context and emit one φ per live output. The φ nodes share the guard and read only the selected operand |
| Trans-Prog | Emit parameter nodes, then select the return slot as the single root of an ordinary numbered PEG |
| Trans-While | Typed source syntax and finite executions. A manually wired θ/pass/eval PEG agrees with every successful execution of the factorial fixture |
| Theorem 2 | `Program.translate_returns` takes a successful source execution and proves the exact defined value at the translated PEG root |

Variables are typed positional slots. The paper’s update of a named binding
is represented by assignment followed by a projection dropping the old
slot. Programs have one entry body and a typed return slot. The primitive
interpretation supplies the carrier and deterministic pure partial
operations for both source and target. Expressions apply these strictly.
There are no source effects, observable evaluation order within a primitive’s
argument list, or trap payloads. `Exec` runs a sequence in order and evaluates
only the selected branch. It records primitive undefinedness as finite
failure, and divergence means absence of a finite execution.
`Exec.deterministic` gives uniqueness of the outcome of a finite execution.
[Source definitions](../../Silmaril/SSA/PEG/Simple/Defs.lean)

`Stmt.lower_correct` preserves all live slots from a realized initial
context. `Code.observe_toGraph` connects emission-order evaluation to the
unique Figure 11 denotation. `Program.translate_wellFormed` supplies the
structural guard for that denotation directly from the translation.
`Program.translate_returns` needs only the source execution and return
value for the given input and interpretation. Because the loop frame is
empty, every index is the paper’s all-zero index.
[Theorem headers](../../Silmaril/SSA/PEG/Simple/Thms.lean)

## Comparison with the authors’ Coq

- `SIMPLER.v` uses a fresh slot via `option V`, a separate `renamer`,
  and binary operators and higher-order application. Lean uses typed slot
  lists and arbitrary-arity opcode applications. Its projection models the
  typed context map, and there is no dedicated higher-order application form.
  [SIMPLER.v](https://cseweb.ucsd.edu/groups/progsys/peg-coq-proof/SIMPLER.v)
- `SIMPLERSem.v` uses coinductive `Delaying` for source computations,
  including operator delay and nonterminating loops. The observation in
  `preserveFunctioner` is finite completion with a specified value. Lean
  gives a separate source observation to finite failure. The target uses
  Figure 11’s single bottom and can return a value even if the source fails
  in a discarded assignment. The fixture checks this example.
  [SIMPLERSem.v](https://cseweb.ucsd.edu/groups/progsys/peg-coq-proof/SIMPLERSem.v) ·
  [TranslaterSem.v](https://cseweb.ucsd.edu/groups/progsys/peg-coq-proof/TranslaterSem.v)
- In `PEGSem.v`, pass runs the Boolean predicate at successive indices
  starting with zero, waiting for each result. Eval waits for its count and
  samples its operand directly at that count. Figure 11 additionally
  requires defined values at every earlier index for eval. Consequently a
  stream with bottom at zero and a defined sample at one can complete under
  Coq eval with a defined count of one, while Figure 11 eval returns bottom.
  Lean uses Figure 11 for both operators. It observes returned values or
  bottom, with no observation of delay steps.
  [PEGSem.v](https://cseweb.ucsd.edu/groups/progsys/peg-coq-proof/PEGSem.v) ·
  [Figure 11](https://arxiv.org/pdf/1012.1802v3#page=23) ·
  [PEG denotation](peg-semantics.md)

## Structured while boundary

`Program.translate` takes `Program P false …`. A follow-up must allocate
distinct loop IDs and simultaneous typed θ slots, lower the guard and body
over those slots, wire the feedback, and produce eval nodes using a common
pass on a negated guard. Guard negation must have the specified semantics
for the chosen instruction set. The compiler must discharge graph scoping
and demand well-foundedness for its output. Preservation must relate each
θ sample through the exit to the corresponding source store. Those facts
give the false prefix of the exit predicate, the first true at the exit,
and the defined data prefix required by eval. In a nested loop they must
hold at fixed enclosing coordinates. The factorial fixture proves the first
exit and both eval prefixes for arbitrary natural inputs. It checks the
observations for zero iterations and for ten iterations.
[Lean fixture](../../tests/ssa/PEGSimple.lean)

## Replay

```sh
lake build --wfail +Silmaril.SSA.PEG.Simple.Thms PEGCoreTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGSimple.lean
lake env leanchecker Silmaril.SSA.PEG.Simple.Thms
lake env leanchecker tests.ssa.PEGSimple
make check CHECK_TARGETS='+Silmaril.SSA.PEG.Simple.Thms PEGCoreTests'
```
