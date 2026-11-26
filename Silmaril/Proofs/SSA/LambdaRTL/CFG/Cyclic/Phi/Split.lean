module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Defs

public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.Split

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Row)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)

universe w
variable {V W K J : Type w} [DecidableEq K] [DecidableEq J] (plan : Plan V W K J)

omit [DecidableEq J] in
private theorem rekey_injective (target : K) : Function.Injective (plan.rekey target) := by
  intro a b equal
  by_cases ha : plan.selected a target <;> by_cases hb : plan.selected b target
  · exact (ha.1).trans hb.1.symm
  · cases b with
    | none => simp [Plan.rekey, ha, hb] at equal
    | some b => simp [Plan.rekey, ha, hb, Ne.symm (plan.fresh b)] at equal
  · cases a with
    | none => simp [Plan.rekey, ha, hb] at equal
    | some a => simp [Plan.rekey, ha, hb, plan.fresh a] at equal
  · exact Option.map_injective plan.label.injective (by simpa [Plan.rekey, ha, hb] using equal)

private theorem lookup_column (target : K) (pred : Option K) (entries : List (Option K × Val V)) :
    (entries.map fun (k, value) => (plan.rekey target k, value.rename plan.register)).lookup
        (plan.rekey target pred) =
      (entries.lookup pred).map (Val.rename plan.register) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨key, value⟩ := entry
    by_cases hit : pred = key
    · subst key
      simp
    · have missed := beq_eq_false_iff_ne.mpr hit
      have mappedMiss := beq_eq_false_iff_ne.mpr (fun equal => hit (rekey_injective plan target equal))
      simp only [List.map_cons, List.lookup_cons, missed, mappedMiss, ih]

theorem operand_rename (target : K) (pred : Option K) (row : Row V K) :
    (plan.renameRow target row).operand (plan.rekey target pred) =
      (row.operand pred).rename plan.register := by
  unfold Plan.renameRow Row.operand
  rw [lookup_column]
  cases row.incoming.lookup pred <;> rfl

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.Split
