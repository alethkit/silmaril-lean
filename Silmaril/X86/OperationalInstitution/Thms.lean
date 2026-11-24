module

public import Silmaril.X86.OperationalInstitution.Defs

@[expose] public section

namespace Silmaril.X86.OperationalInstitution

/-- Going steps of the register view are exactly the live machine's going steps. -/
theorem step_iff {σ : Type} (A : RelIsa σ) (s t : σ) :
    (system A).model (encode A.toViews (some s), (), encode A.toViews (some t)) ↔
      A.live s ∧ A.step s (.ok t) := by
  change (encode A.toViews (some s) = _ ∧ encode A.toViews (some t) = _ ∧ _) ↔ _
  simp [encode]

/-- The terminal edge records precisely the live machine's explicit stop. -/
theorem stop_iff {σ : Type} (A : RelIsa σ) (s : σ) :
    (system A).model (encode A.toViews (some s), (), encode A.toViews none) ↔
      A.live s ∧ A.step s .stop := by
  change (encode A.toViews (some s) = _ ∧ encode A.toViews none = _ ∧ _) ↔ _
  simp [encode]

/-- The canonical stopped configuration cannot take a further step. -/
theorem stopped_no_step {σ : Type} (A : RelIsa σ) (dst : (shape σ).Config) :
    ¬ (system A).model (encode A.toViews none, (), dst) :=
  id

end Silmaril.X86.OperationalInstitution
