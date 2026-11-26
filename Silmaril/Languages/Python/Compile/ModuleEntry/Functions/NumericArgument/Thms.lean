module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.Defs
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

theorem power_iff {base exponent result : Int} :
    power? base exponent = some result ↔
      0 ≤ exponent ∧ (base.natAbs.log2 + 1) * exponent.toNat ≤ 4096 ∧ result = base ^ exponent.toNat := by
  unfold power?
  split <;> simp_all [eq_comm]

theorem power_magnitude {base exponent result : Int} (checked : power? base exponent = some result) :
    result.natAbs < 2 ^ 4096 :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.power_magnitude checked

theorem check_power {left right : Source.Expr} {base exponent result : Int}
    (lhs : integer? left = some base) (rhs : integer? right = some exponent)
    (checked : power? base exponent = some result) :
    check (.binary .pow left right) = some (.integer result) := by
  simp [check, integer?, lhs, rhs, binary?, checked]

theorem testBit_bitwise (operation : Bool → Bool → Bool) (left right : Int) (index : Nat) :
    testBit (bitwise operation left right) index = operation (testBit left index) (testBit right index) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.testBit_bitwise operation left right index

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument
