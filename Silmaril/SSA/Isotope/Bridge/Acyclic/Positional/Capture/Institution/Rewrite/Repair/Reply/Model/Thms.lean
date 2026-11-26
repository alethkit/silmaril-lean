module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Model.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Execution
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Separation

/-! # Validated reflection of finite binary-reply trees -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

open Kleisli (value)
open LambdaSSA.Region (packedExitType)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

local notation "J" => Kleisli.J (m := Trace)

theorem modelCoherent :
    letI := Kleisli.instructions model
    LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := signature.Instr) J Kleisli.types :=
  Kleisli.regionCoherent model model_pure_proof (Tagged.ofOutcomes ∅)

/-- The separator is a member of the existing validated captured room. -/
noncomputable def separator : (grammarRoom J signature).Mod :=
  Kleisli.validated model modelCoherent

theorem Tree.programOutcomes_eq (tail : List Sorts) (p : Tree) :
    p.programOutcomes tail =
      p.normal.outcomes (Sum.inl PUnit.unit : value (packedExitType (Ty.unit :: tail))) :=
  programOutcomes_proof tail p

theorem programOutcomes_iff_normal (tail : List Sorts) (p q : Tree) :
    p.programOutcomes tail = q.programOutcomes tail ↔ p.normal = q.normal := by
  rw [p.programOutcomes_eq, q.programOutcomes_eq]
  exact ⟨fun h => outcomes_injective_proof _ h, congrArg (Normal.outcomes _)⟩

/-- The slice after the first recorded reply is the chosen continuation's
actual packed observation, with its other replies still present. -/
theorem programAfterReply (tail : List Sorts) (req bound right : Bool) (l r : Tree) :
    afterReply req right ((Tree.ask req bound l r).programOutcomes tail) =
      (if right then r else l).programOutcomes tail := by
  rw [Tree.programOutcomes_eq, Tree.programOutcomes_eq, Tree.normal]
  have h := afterReply_outcomes_proof (Sum.inl PUnit.unit : PUnit ⊕ value (packedExitType tail))
    req right l.normal r.normal
  cases right <;> exact h

theorem separator_sat_iff_normal (tail : List Sorts) (p q : Tree) :
    (grammarRoom J signature).Sat separator (equation tail p q) ↔ p.normal = q.normal :=
  (Kleisli.validated_sat_iff model modelCoherent _).trans
    ⟨fun h => (programOutcomes_iff_normal tail p q).mp (programOutcomes_eq_of_sat_proof tail p q h),
      fun h => Kleisli.sat_of_repaired model model_pure_proof _ (repaired_of_normal tail p q h)⟩

theorem separator_sat_iff_repaired (tail : List Sorts) (p q : Tree) :
    (grammarRoom J signature).Sat separator (equation tail p q) ↔ Repaired false (equation tail p q) :=
  ⟨fun h => repaired_of_normal tail p q ((separator_sat_iff_normal tail p q).mp h),
    fun h => (Kleisli.validated_sat_iff model modelCoherent _).mpr
      (Kleisli.sat_of_repaired model model_pure_proof _ h)⟩

theorem repaired_of_validated_valid (tail : List Sorts) (p q : Tree)
    (valid : ∀ K : (grammarRoom J signature).Mod, (grammarRoom J signature).Sat K (equation tail p q)) :
    Repaired false (equation tail p q) :=
  (separator_sat_iff_repaired tail p q).mp (valid separator)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
