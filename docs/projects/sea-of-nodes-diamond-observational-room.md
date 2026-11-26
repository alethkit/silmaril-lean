# Generated diamonds in the existing λSSA observational room

```lean
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber.Thms
```

For each native signature `P`, `fixedFiber P` is the existing one-exit
`lambdaSSA` institution at the exact alphabet `Primitive P.op`. It is
indexed by the number of ambient bound values. `scope` takes the actual
emitted CFG and derives a scope witness from its typing.
`translateEquation` constructs the existing observational equation between
the scoped CFGs at the length of their common input context.
[Existing observational API](../../Silmaril/SSA/Isotope/Institution/Observational/Thms.lean) ·
[Fiber definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/LambdaSSA/Institution/Fiber/Defs.lean) ·
[Generated room (#3347)](https://github.com/hiloopai/silmaril-lean/pull/3347)

At a native model and typed input, `inputModel` uses the lowering's tagged
atoms and primitive interpretation. Its bound value at position `i` is
`inputEnv m input i`. The existing scope theorem identifies execution under
that model's bound environment with execution under the original encoding.
`ret_mem_eval` gives this equality of return observations by membership.
`ret_mem_unit_eval` factors each return observation into a finite unit-state
evaluation and equality of the initial and final states.
`fault_absent` uses the empty primitive fault relation. `divergence_absent`
uses a successful deterministic execution at the encoded input and the
empty primitive divergence predicate.

`room_satisfaction_at` equates full behaviour equality in the existing
room with unit-state finite observation agreement at the chosen input.
The ambient state type can be any inhabited type. Returns preserve the
initial state, and any inhabitant gives a witness for reflection from
behaviour equality. With an empty state carrier all behaviours are empty,
so the translated equation holds even for unequal diamonds.
`room_satisfaction` quantifies over the induced models for every typed
input, and `translated_satisfaction` composes this with the native equation
iff. The fixed-alphabet fibers and their scope indexing are the domain of
this factorization.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/LambdaSSA/Institution/Fiber/Thms.lean) ·
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/LambdaSSA/Institution/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Regression'
```
