module

public import Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Defs

/-! Normalize a native word program with checked right identities and exact GVN keys. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.WordNormalize

open Diamond (ValueSort)

scoped instance : DecidableEq (ValueSort Unit) := fun a b =>
  match a, b with
  | .predicate, .predicate | .data (), .data () => isTrue rfl
  | .predicate, .data _ | .data _, .predicate => isFalse (fun h => by cases h)

scoped instance (ins : List (ValueSort Unit)) (out : ValueSort Unit) :
    DecidableEq (SubZero.Opcode ins out) := fun a b => by
  cases a <;> cases b
  case literal.literal x y =>
    exact if h : x = y then isTrue (congrArg SubZero.Opcode.literal h)
      else isFalse (fun same => h (SubZero.Opcode.literal.inj same))
  all_goals first | exact isTrue rfl | exact isFalse (by intro h; cases h)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

/-- Apply one GVN deletion and route the old return into the rewritten table. -/
def gvnStep? (program : Program SubZero.Opcode inputs out) : Option (Program SubZero.Opcode inputs out) :=
  (GVN.Pass.step? program.dataflow).map fun rewrite =>
    { sigs := rewrite.sigs', dataflow := rewrite.flow, result := rewrite.route program.result }

/-- Prefer an identity deletion. Recompute both searches on each new program. -/
def step? (program : Program SubZero.Opcode inputs out) : Option (Program SubZero.Opcode inputs out) :=
  (RightIdentityPass.step? program).orElse fun _ => gvnStep? program

/-- Neither matcher accepts a deletion in the current table. -/
def Normal (program : Program SubZero.Opcode inputs out) : Prop :=
  RightIdentityPass.Normal program ∧ GVN.Pass.NoDuplicate program.dataflow

/-- Each success removes one binding, so the initial count suffices as fuel. -/
def normalize (program : Program SubZero.Opcode inputs out) : RightIdentityPass.Result inputs out :=
  RightIdentityPass.runWith step? program.sigs.length program

end Silmaril.SSA.SeaOfNodes.Pure.WordNormalize
