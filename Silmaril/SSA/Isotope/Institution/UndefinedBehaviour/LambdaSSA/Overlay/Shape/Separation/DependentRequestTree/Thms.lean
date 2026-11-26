module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Soundness
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Separation

/-! # Exact shaped refinement of finite typed request trees -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree

open Category.FiniteIteration.Syntax (Bindings model)
open TwoRequest (resultBehaviour)

universe u v w

variable {Φ : Type u} [HasTy Φ (Silmaril.Ty Empty)] {S : RequestSignature Φ}

/-- It suffices to compare continuations at reachable typed replies.
This soundness direction permits arbitrary shaped primitive relations. -/
theorem shaped_sound (p q : Tree S.replies) (h : p.Refines q) {Γ : List (Silmaril.Ty Empty)}
    (M : Shape.Model.{u,0,v,w} Φ Γ) (s : M.raw.σ) :
    Shape.denote (p.region S) M s ≤ Shape.denote (q.region S) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.shaped_sound p q h M s

/-- Tag dispatch through the actual native request and typed packet router
preserves the complete deterministic observation. -/
theorem finite_observe {Γ : List (Silmaril.Ty Empty)} {n : Nat} (p : Tree S.replies) (h : Handler S.replies n)
    (env : Bindings Γ) (s : Fin n) :
    Shape.denote (p.region S) (model (S.primitives h) env) s = resultBehaviour (p.execute h s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.finite_observe p h env s

/-- The comparison of two occurrences of the same zero-reply key has no
branch obligations. Both occurrences still execute the request. -/
theorem empty_reply_refines {f : Φ} (h : S.replies f = [])
    (arms next : Fin (S.replies f).length → Tree S.replies) :
    (Tree.ask f arms).Refines (Tree.ask f next) :=
  ⟨rfl, fun i => (i.cast (congrArg List.length h)).elim0⟩

/-- One state per common reply plus a final test state distinguishes a
failed comparison. The prefix is bounded by both depths. -/
theorem exists_prefix_countermodel [DecidableEq Φ] {p q : Tree S.replies} (fails : ¬ p.Refines q) :
    ∃ (n : Nat) (probe : Prefix S.replies n), n ≤ min p.depth q.depth ∧
      ¬ Shape.denote (p.region S) (S.model probe.handler) 0 ≤
        Shape.denote (q.region S) (S.model probe.handler) 0 :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.exists_prefix_countermodel fails

/-- All-model validity at the finite witnesses' universes. Soundness also
holds at arbitrary value and machine state universes. -/
theorem shaped_refines_iff [DecidableEq Φ] (p q : Tree S.replies) :
    (∀ (M : Shape.Model.{u,0,0,0} Φ []) (s : M.raw.σ),
      Shape.denote (p.region S) M s ≤ Shape.denote (q.region S) M s) ↔ p.Refines q := by
  refine ⟨fun all => Classical.byContradiction fun bad => ?_, fun h M s => shaped_sound p q h M s⟩
  obtain ⟨_, probe, _, separated⟩ := exists_prefix_countermodel bad
  exact separated (all (S.model probe.handler) 0)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
