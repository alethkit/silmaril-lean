module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Exits.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Execution
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Recovery
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Replay

/-! # Native replay and validated reflection of finite payload tables -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

open Isotope.LetCase.LocallyNameless (Equiv)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

local notation "J" => Kleisli.J (m := Trace)

/-- Native sum η and unit η with pure let β turn a live bit into its two
constructor entries. The table retains the expression's two values. -/
theorem Expr.replay (e : Expr) {n : Nat} (β : BoundCtx Sorts n) (i : Fin n)
    (h : β.get i = Bit) :
    Equiv false (Ctx.nil : Ctx Empty Sorts) β (e.operand β i h).1
      ((Expr.table (e.evaluate false) (e.evaluate true)).operand β i h).1 Bit :=
  expr_replay_proof e β i h

/-- Replay in the actual packed terms, including effectful case binding
and the shared native exit continuation. -/
theorem derive_normal (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L))
    (h : p.normal = q.normal) : Derivable false (equation H L p q) :=
  derive_normal_proof H L p q h

theorem derive_render (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    Derivable false (equation H L p p.normal.render) :=
  derive_render_proof H L p

/-- The free-type trace algebra has coherent native region witnesses. -/
theorem modelCoherent :
    letI := Kleisli.instructions model
    LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := signature.Instr) J Kleisli.types :=
  Kleisli.regionCoherent model model_pure_proof (Tagged.ofOutcomes ∅)

/-- The separator belongs to the existing validated room at the reply-payload signature. -/
noncomputable def separator : (grammarRoom J signature).Mod :=
  Kleisli.validated model modelCoherent

/-- The actual packed term has the independently enumerated observations. -/
theorem programOutcomes_eq (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L)) :
    programOutcomes H L p = p.normal.outcomes :=
  programOutcomes_proof H L p

/-- The exact reply fields, ordered effects, exit position, and result recover
the normal form. Distinct source expressions can have the same table. -/
theorem programOutcomes_iff_normal (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) :
    programOutcomes H L p = programOutcomes H L q ↔ p.normal = q.normal := by
  rw [programOutcomes_eq, programOutcomes_eq]
  exact ⟨fun h => outcomes_injective_proof _ h, congrArg Normal.outcomes⟩

/-- Observe one selected reply value at its original arm and ordered exit. -/
theorem programAfterPayload (H : Sorts) (L : List Sorts) (p : ProgramBody (H :: L))
    (right b : Bool) :
    afterPayload p.request right b (programOutcomes H L p) =
      ((if right then p.normal.right else p.normal.left).traceTree b).outcomesWith Exits.Exit.packed :=
  (congrArg (afterPayload p.request right b) (programOutcomes_eq H L p)).trans
    (afterPayload_proof p.normal right b)

theorem separator_sat_iff_normal (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ p.normal = q.normal :=
  (Kleisli.validated_sat_iff model modelCoherent _).trans
    ⟨fun h => (programOutcomes_iff_normal H L p q).mp (programOutcomes_eq_of_sat_proof H L p q h),
      fun h => Kleisli.sat_of_repaired model model_pure_proof _ (Repaired.ofNative (derive_normal H L p q h))⟩

theorem separator_sat_iff_repaired (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L)) :
    (grammarRoom J signature).Sat separator (equation H L p q) ↔ Repaired false (equation H L p q) :=
  ⟨fun h => Repaired.ofNative (derive_normal H L p q ((separator_sat_iff_normal H L p q).mp h)),
    fun h => (Kleisli.validated_sat_iff model modelCoherent _).mpr
      (Kleisli.sat_of_repaired model model_pure_proof _ h)⟩

/-- Validity in the whole existing model class reflects to the native rules on
this fragment. Its replay requires only the original LetCase equations. -/
theorem derive_of_validated_valid (H : Sorts) (L : List Sorts) (p q : ProgramBody (H :: L))
    (valid : ∀ K : (grammarRoom J signature).Mod, (grammarRoom J signature).Sat K (equation H L p q)) :
    Derivable false (equation H L p q) :=
  derive_normal H L p q ((separator_sat_iff_normal H L p q).mp (valid separator))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
