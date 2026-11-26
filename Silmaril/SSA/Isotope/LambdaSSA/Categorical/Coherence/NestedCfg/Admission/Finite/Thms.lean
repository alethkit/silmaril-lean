module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmission
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax

/-! # Witness coherence for an admitted finite retained inner interface -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

/-- Successful traversal records exact label reindexing, checked branch
operands and written paths to each retained input. -/
theorem check?_sound {k n : Nat} {keep : Fin (k + 1) ↪ Fin (n + 1)} {P : Fin (k + 1) → Ty Empty}
    {r : Region Φ} {p : Plan Φ (k + 1) (n + 1)} {L : LCtx (Ty Empty)}
    (ok : check? keep P r L = some p) : p.Valid keep P r L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax.valid ok

/-- Invert any exact typing of the compact original inner code. The types of
the retained rows are forced by the checked entry and written paths. -/
theorem Plan.Valid.retained_types {k n : Nat} {keep : Fin (k + 1) ↪ Fin (n + 1)}
    {P S : Fin (k + 1) → Ty Empty} {r : Region Φ} {p : Plan Φ (k + 1) (n + 1)}
    {L K : LCtx (Ty Empty)} (checked : p.Valid keep P r L)
    (entry : p.entry.HasType [p.payload] (List.ofFn S ++ K))
    (rows : ∀ i, (p.rows (keep i)).HasType [S i, p.payload] (List.ofFn S ++ K)) : S = P :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax.aligned true
    checked.entryRoute checked.rowRoutes entry rows checked.paths

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

/-- Compare two original exact witnesses at a successful finite mask and
payload check. Rolling trims each inner witness. The existing pure
uniformity and exit naturality compare the inner and outer arrows. -/
theorem compare?_sound (roll : IterationRolling C) {k n : Nat} {keep : Fin (k + 1) ↪ Fin (n + 1)}
    {P : Fin (k + 1) → Ty Empty} {r : Region Φ} {L : LCtx (Ty Empty)}
    {h h' : r.HasType [] L}
    {f g : J.obj (ctxObj M []) ⟶ J.obj (labelObj M L)}
    (ok : compare? keep P r L = .certified) (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) :
    f = g := by
  cases checked : check? keep P r L with
  | none => simp [compare?, checked] at ok
  | some p =>
      exact Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmission.compare_finite J M roll
        (check?_sound checked) left right

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite
