# Normalize a pure Simple word program

`WordNormalize.normalize` combines the checked Simple chapter 8
right identities with exact-key GVN over the native `Pure.Program`
table. It tries a right identity first. If that scan fails, it tries
one GVN deletion and applies the verified routing to the return wire.
Every new step uses the current shortened table.
[Right identities and pinned Simple sources](sea-of-nodes-pure-right-identity-pass.md) ·
[Exact-key GVN and Click PLDI ’95 §3.1](sea-of-nodes-gvn-pass.md) ·
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/WordNormalize/Defs.lean)

```lean
module

public import Silmaril.SSA.SeaOfNodes.Pure.WordNormalize.Defs

@[expose] public section

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure

def optimize {inputs : List (Diamond.ValueSort Unit)} {out : Diamond.ValueSort Unit}
    (program : Program SubZero.Opcode inputs out) : Program SubZero.Opcode inputs out :=
  (WordNormalize.normalize program).program
```

Call `(optimize program).lower` to emit the existing typed RVSDG
representation. `WordNormalize.normalize_lower_run_eq` proves that
the emitted graph returns the same singleton tuple on every typed
input in the modular word model.
[Proof API](../../Silmaril/SSA/SeaOfNodes/Pure/WordNormalize/Thms.lean)

`step_size` proves that either successful rewrite deletes exactly one
binding. `normalize_count` accounts for each deletion and bounds them
by the original table length. If the driver uses all available fuel,
the table is empty and a further shrinking step is impossible.
`normalize_normal` proves that the final table has neither a
checker-accepted right identity nor an exact-key GVN duplicate.
`normalize_eval_eq` proves equality of native returns for all typed
inputs.

The fixture starts with `(x + 0) - y` and `x - y` at different
structural keys. Identity erasure makes those keys equal. GVN then
redirects a downstream subtraction, leaving the reversed `y - x`
binding, and the emitted result wraps to `0xfffffffffffffffe` on
inputs 0 and 1. In the other direction, an exact-key replacement
retains the opcode and literal payload of the replaced producer,
so turning a nonliteral right operand into a literal is unavailable
to this GVN matcher.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/WordNormalize/Regression.lean)

The fixed point is relative to the two supported matchers and the
chosen order. The table is pure and acyclic. Constant inference,
operand commutation, and unrelated dead binding removal are outside
this pass.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.WordNormalize.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Pure.WordNormalize.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.WordNormalize.Regression
```
