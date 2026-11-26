module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Model.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Packing
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Reflection

/-! # Reflection at the original typed exit positions -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits

local notation "J" => Kleisli.J (m := Trace)

/-- The packed success value determines the position and its typed payload. -/
theorem Exit.packed_injective (L : List Sorts) : Function.Injective (@Exit.packed L) :=
  packed_injective_proof L

/-- The actual packed emitted terms replay the same case and abort rules
under the shared native exit continuation. -/
theorem repaired_of_normal (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L)))
    (h : p.normal = q.normal) : Repaired false (equation H L p q) :=
  repaired_of_normal_proof H L p q h

/-- Observations of the captured term retain the original outward tag in
each successful leaf. -/
theorem programOutcomes_eq (H : Sorts) (L : List Sorts) (p : Tree (Exit (H :: L))) :
    programOutcomes H L p = p.normal.outcomesWith Exit.packed :=
  programOutcomes_proof H L p

theorem programOutcomes_iff_normal (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L))) :
    programOutcomes H L p = programOutcomes H L q ↔ p.normal = q.normal := by
  rw [programOutcomes_eq, programOutcomes_eq]
  exact ⟨fun h => Normal.outcomesWith_injective _ (Exit.packed_injective _) h,
    congrArg (Normal.outcomesWith Exit.packed)⟩

theorem programAfterReply (H : Sorts) (L : List Sorts) (req bound right : Bool)
    (l r : Tree (Exit (H :: L))) :
    afterReply req right (programOutcomes H L (.ask req bound l r)) =
      programOutcomes H L (if right then r else l) := by
  rw [programOutcomes_eq, programOutcomes_eq, Tree.normal]
  have h := Normal.afterReply_outcomesWith (@Exit.packed (H :: L)) req right l.normal r.normal
  cases right <;> exact h

theorem separator_sat_iff_normal (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L))) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ p.normal = q.normal :=
  (Reply.separator_sat_iff _).trans
    ⟨fun h => (programOutcomes_iff_normal H L p q).mp (programOutcomes_eq_of_sat_proof H L p q h),
      fun h => Kleisli.sat_of_repaired model model_respectsPure _ (repaired_of_normal H L p q h)⟩

theorem separator_sat_iff_repaired (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L))) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ Repaired false (equation H L p q) :=
  ⟨fun h => repaired_of_normal H L p q ((separator_sat_iff_normal H L p q).mp h),
    fun h => (Reply.separator_sat_iff _).mpr (Kleisli.sat_of_repaired model model_respectsPure _ h)⟩

theorem repaired_of_validated_valid (H : Sorts) (L : List Sorts) (p q : Tree (Exit (H :: L)))
    (valid : ∀ K : (grammarRoom J signature).Mod, (grammarRoom J signature).Sat K (equation H L p q)) :
    Repaired false (equation H L p q) :=
  (separator_sat_iff_repaired H L p q).mp (valid separator)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Exits
