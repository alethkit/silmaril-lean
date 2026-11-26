module

public import Silmaril.Logic.Temporal.TLA.StutterReduction.Thms

public section

namespace Silmaril.Logic.Temporal.TLA.StutterReduction.Examples

def repeatTwice : Retiming where
  index n := n / 2
  zero := rfl
  step n := by omega
  cofinal j := ⟨2 * j, by omega⟩

/-- `0, 1, 2, 2, …` -/
def finiteChanges : Behavior Nat := fun n => min n 2

/-- `0, 1, 0, 1, …` -/
def infiniteChanges : Behavior Nat := fun n => n % 2

/-- `0, 0, 1, 1, 2, 2, …` reduces to `0, 1, 2, 2, …`. -/
theorem finiteChanges_reduce :
    (finiteChanges.retime repeatTwice).canonicalReduction = finiteChanges := by
  rw [Behavior.canonicalReduction_retime]
  apply Behavior.canonicalReduction_of_reduced
  intro i same j hij
  simp only [finiteChanges] at same ⊢
  omega

/-- `0, 0, 1, 1, 0, 0, 1, 1, …` reduces to `0, 1, 0, 1, …`. -/
theorem infiniteChanges_reduce :
    (infiniteChanges.retime repeatTwice).canonicalReduction = infiniteChanges := by
  rw [Behavior.canonicalReduction_retime]
  apply Behavior.canonicalReduction_of_reduced
  intro i same
  simp only [infiniteChanges] at same
  omega

/-- Repeating states in either input cannot equate these finite and infinite change patterns. -/
theorem finiteChanges_not_stutterEquiv_infiniteChanges :
    ¬ StutterEquiv (finiteChanges.retime repeatTwice) (infiniteChanges.retime repeatTwice) := by
  rw [← Behavior.canonicalReduction_eq_iff_stutterEquiv, finiteChanges_reduce, infiniteChanges_reduce]
  intro eq
  have atTwo := congrFun eq 2
  simp [finiteChanges, infiniteChanges] at atTwo

end Silmaril.Logic.Temporal.TLA.StutterReduction.Examples
