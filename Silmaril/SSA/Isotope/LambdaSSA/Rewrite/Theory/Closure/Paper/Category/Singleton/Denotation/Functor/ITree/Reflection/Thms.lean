module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonFreeITreeReflection

/-! # Failure of reflection for guarded singleton arrows in free typed weak ITrees

The two acyclic arrows implement the same tag swap and the same visible
primitive branch. The source separates a case inside a returned term from the
corresponding region case. Its lawful observation preserves every constructor
of the default guarded relation, including CFG and substitution rules.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ITree.Reflection

open CategoryTheory Silmaril.Elgot.ITree
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- The term-case arrow computes the shared tree for every typed input. -/
theorem termArrow_behavior (a : InputValue) : run termArrow a = behavior a :=
  SingletonFreeITreeReflection.termArrow_behavior a

/-- The region-case arrow computes the shared tree for every typed input. -/
theorem regionArrow_behavior (a : InputValue) : run regionArrow a = behavior a :=
  SingletonFreeITreeReflection.regionArrow_behavior a

/-- The two arrows have identical weak trees, including every typed reply
continuation, but are distinct in the default guarded singleton quotient. -/
theorem separation :
    interpretation.map termArrow = interpretation.map regionArrow ∧ termArrow ≠ regionArrow :=
  ⟨SingletonFreeITreeReflection.sameImage, SingletonFreeITreeReflection.distinct⟩

/-- A source observation invariant under all default equations separates the
two representatives at a typed input. -/
theorem separatingObserver :
    ∃ observe : Region Op → Bool,
      (∀ {r s}, Paper.Eqv [Input] r s [Output] → observe r = observe s) ∧
      observe termCase ≠ observe regionCase :=
  SingletonFreeITreeReflection.separatingObserver

/-- The first observation on the right branch is a real request. Its result
contains whichever tag and number the handler supplies. -/
theorem visible_poll (operand : Nat) :
    out (run termArrow (.inr ⟨operand⟩)) =
      Part.some (.vis (.request .poll operand) (fun b => pure (reply b))) :=
  (congrArg out (termArrow_behavior (.inr ⟨operand⟩))).trans (out_vis _ _)

/-- The profile separates different primitive requests. Weak equality
retains both the opcode and the full numeric operand. -/
theorem request_injective :
    Function.Injective (fun call : Op × Nat =>
      (vis (.request call.1 call.2) (fun b => pure (reply b)) : TreeModel OutputValue)) :=
  SingletonFreeITreeReflection.request_injective

/-- Faithfulness fails for the free typed weak ITree functor in this profile. -/
theorem not_faithful : ¬ interpretation.Faithful :=
  fun h => separation.2 (h.map_injective separation.1)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ITree.Reflection
