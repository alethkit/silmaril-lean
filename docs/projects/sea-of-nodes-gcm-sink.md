# Sinking one pure let into its consuming λSSA arm

`sink?` matches and rewrites an actual λSSA region with one entry and two
successor blocks. The entry receives a selector of type `unit + unit`,
an operand of type `A`, and an independent fallback of type `B`. The moved
opcode has type `A → B`. Both original arms forward their own parameter to
external exit zero. The matcher checks the entry and both arm bodies, so it
admits just the use on the left transfer and its forwarding arm.
[Definitions][defs] · [Typing and execution][thms]

| Position | Before | After |
| --- | --- | --- |
| Entry | Compute the result and branch. Pass the result on edge zero and the fallback on edge one. | Branch on the same selector. Pass the original operand on edge zero and the fallback on edge one. |
| Block zero | Return its parameter of type `B`. | Compute from its parameter of type `A` and return the new `B`. |
| Block one | Return the fallback parameter of type `B`. | Return the fallback parameter of type `B`. |

The pass changes the left block’s parameter type and the argument of its
incoming branch together. Block bodies use the environment captured at the
CFG boundary plus the argument of the taken branch. Passing the operand
explicitly makes it available inside the block. The fresh left result
has one use, the exit payload.
[λSSA operational semantics][semantics]

## Placement constraints

In Click’s PLDI ’95 terminology, operand availability constrains schedule
early and uses constrain schedule late. Section 2.3 places a Phi input's
use at the corresponding predecessor transfer. The cut convention of the
merged placement checker can describe the two situations here.

- Before motion, the original operand is an entry argument available at
  cut zero. The computed result is read by argument zero of the precise
  left occurrence in the entry terminator, at cut one after its let.
  This is the incoming-use convention of `Use.phi`.
- After routing the original operand on that edge, the left parameter is
  available at cut zero of its block. The forwarding exit payload is an
  ordinary read at that same insertion cut in the body without the let.
  The new let runs after parameter binding and before that read. In the
  emitted body the exit read is at cut one, after the inserted let.

The original incoming use lies in the predecessor, so it would fail a
placement check for a result defined in the successor. The rewrite changes
that edge and the consuming block together. The cut correspondence
describes the admitted sites. The proof checks the actual λSSA terms
directly. [Placement checker][checker] · [PLDI ’95 §§2.2–2.4][paper] ·
[Archived PDF][pdf]

## Finite returns

`sink?_eval_iff` preserves and reflects `Region.Eval` for every entry
environment, exit label, payload and ambient state, whenever the rewrite
returns a region. The model interprets the moved primitive as a total
function on tagged values and leaves the ambient state unchanged.
`after_eval_iff` gives the exact observation. A left tag returns the
computed result, a right tag returns the independent fallback for any value
of the operand, and a non-sum selector has no finite return. Every finite
return is at exit zero with the original state.

The fixture inspects the actual CFG entry and both block bodies before and
after the rewrite. It also exercises both arms, changes the unused operand
on right-arm inputs, and checks rejection when both edges read the let.
The profile covers this one acyclic transformation. Loop-depth selection,
general code motion, and moving partial, trapping or effectful operations
are outside the profile. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.Sink.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.Sink.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.Regression
```

[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/Sink/Defs.lean
[thms]: ../../Silmaril/SSA/SeaOfNodes/GCM/Sink/Thms.lean
[semantics]: ../../Silmaril/SSA/Isotope/LambdaSSA/Defs.lean
[checker]: sea-of-nodes-gcm-legality.md
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/Sink/Regression.lean
[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
