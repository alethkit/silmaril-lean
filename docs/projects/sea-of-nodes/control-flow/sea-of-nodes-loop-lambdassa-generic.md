# Generate λSSA for the pure single-loop profile

`Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms` covers every graph
of the [single-loop profile in #3192](https://github.com/hiloopai/silmaril-lean/pull/3192).
`lower g` emits an ordinary λSSA CFG with one local header. The preheader
and each header activation emit one let per producer in dependency order.
The header unpacks the carried tuple and retains the captured function
inputs. The compiled predicate variable controls a λSSA case. Its true
branch transfers the next tuple to label zero, and its false branch
transfers a singleton result at raw label one, which exits at label zero.

`phiView g` records the preheader branch and the header's true branch
as two incoming occurrences. `entry_latch` and `feedback_latch` relate
their entire argument columns to source wire reads. All feedback operands
use the same old activation. This follows the instance of Region/Phi
alignment in [Click and Paleczny, IR ’95 §§2.3 and 3.1–3.2](https://doi.org/10.1145/202530.202534)
and the pinned [Simple evaluator's two-phase loop latch](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L93-L151).

Import `Loop.LambdaSSA.Generic.Reindex.Thms` to enumerate the actual
incoming header branches in either predecessor order.
`headerIncomingEquiv` identifies exactly the preheader jump and the
selected feedback leaf at label zero. `slot_branch_roundtrip` recovers
the original packed branch term through its position in any order,
and `slot_transfer_iff` reads the complete position's column in one
old environment. `header_backedge_iff` checks the actual emitted header
against the native step, including the whole typed feedback packet.

`lower_hasType` checks the generated region for arbitrary typed input,
carried and result profiles. `body_eval` runs the header producer table
and terminator in the unpacked environment. `follow_iff` compares finite
λSSA control execution with the source's counted relation, and
`returns_iff` compares whole-region finite returns in both directions.
The source and target share the total primitive model from the
[scheduled diamond bridge](sea-of-nodes-diamond-lambdassa.md).
The result observes the encoded value at external label zero and
unchanged ambient state. The profile is pure and contains one header,
one entry occurrence and one backedge.

The fixtures use a heterogeneous natural/predicate carried tuple,
including a predicate result on the first activation and after three
backedges. Reversing the predecessor order preserves the original entry
and feedback branches. The changed feedback packet `(0, true)` follows
entry `(1, false)`. Actual header evaluation rejects the two mixed packets.
A second fixture rules out finite returns for a permanently
enabled backedge with an empty carried tuple.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.Regression'
```
