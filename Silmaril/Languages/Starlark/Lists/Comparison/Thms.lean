module

public import Silmaril.Languages.Starlark.Lists.Comparison.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.Comparison.Agreement

public section

namespace Silmaril.Languages.Starlark.Lists.Comparison

/-- Transfer ordered scans from a relational test to its exact result function. -/
theorem scans_iff_scan {α : Type} {tests : α → Except Error Bool → Prop}
    {test : α → Except Error Bool} (agrees : ∀ item out, tests item out ↔ test item = out)
    (decisive : Bool) (items : List α) (out : Except Error Bool) :
    Scans tests decisive items out ↔ scan test decisive items = out :=
  Proofs.Languages.Starlark.Lists.Comparison.scans_iff_scan agrees decisive items out

theorem equalAt_iff (heap : Heap) (depth : Nat) (left right : Value)
    (out : Except Error Bool) :
    EqualAt heap depth left right out ↔ equalAt heap depth left right = out :=
  Proofs.Languages.Starlark.Lists.Comparison.equalAt_iff heap depth left right out

theorem containsAt_iff (heap : Heap) (depth : Nat) (needle target : Value)
    (out : Except Error Bool) :
    ContainsAt heap depth needle target out ↔ containsAt heap depth needle target = out :=
  Proofs.Languages.Starlark.Lists.Comparison.containsAt_iff heap depth needle target out

theorem tests_iff_evaluate (heap : Heap) (left right : Value) (op : ComparisonOp)
    (out : Except Error Bool) :
    Tests heap left right op out ↔ evaluate heap op left right = out :=
  Proofs.Languages.Starlark.Lists.Comparison.tests_iff_evaluate heap left right op out

end Silmaril.Languages.Starlark.Lists.Comparison
