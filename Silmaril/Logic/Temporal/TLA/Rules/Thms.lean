module

public import Silmaril.Logic.Temporal.TLA.Rules.Defs
public import Silmaril.Logic.Temporal.TLA.General.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.Rules.Soundness

/-! Semantic quantifier and refinement rules for standalone TLA. See the
Lamport reference audit in `docs/projects/tla-lamport-audit.md`. -/

public section

namespace Silmaril.Logic.Temporal.TLA

universe u v w x

/-- An auxiliary extension preserves the visible specification if projection is sound
and each satisfying visible run has a pointwise lift. -/
theorem hide_extension_iff {S : Type u} {H : Type v} {p : Behavior S → Prop}
    {q : Behavior (S × H) → Prop} (invariant : StutterInvariant p)
    (sound : General.Refines q Prod.fst p)
    (lift : ∀ σ, p σ → ∃ τ, τ.map Prod.fst = σ ∧ q τ)
    (σ : Behavior S) : hide q σ ↔ p σ :=
  Proofs.Logic.Temporal.TLA.Rules.hide_extension_iff invariant sound lift σ

/-- A refinement that computes a target hidden value and maps the visible state
using only the source's visible state descends through hiding (paper §8.3.2). -/
theorem hide_refines {S : Type u} {H : Type v} {T : Type w} {K : Type x}
    {p : Behavior (S × H) → Prop} {q : Behavior (T × K) → Prop}
    {f : S → T} {g : S × H → K}
    (sim : General.Refines p (fun s => (f s.1, g s)) q) :
    General.Refines (hide p) f (hide q) :=
  Proofs.Logic.Temporal.TLA.Rules.hide_refines sim

/-- A sufficient condition for commuting `ENABLED` with action pullback at `s`.
Only targets of the action from `f s` need to lift. For fairness, use the angle
action as `A`. -/
theorem Action.enabled_pullback_iff {S : Type u} {T : Type v} (f : S → T)
    (A : Action T) (s : S) (lift : ∀ t, A (f s) t → ∃ s', f s' = t) :
    (Action.enabled fun x y => A (f x) (f y)) s ↔ A.enabled (f s) :=
  Proofs.Logic.Temporal.TLA.Rules.enabled_pullback_iff f A s lift

namespace General.Formula

variable {Sorts : Type u} {Value : Sorts → Type u} {Γ : Scope Sorts} {a : Sorts}

/-- Semantic E1 (Fig. 9). Interpret the body in the behavior extended by the
state expression at every instant to obtain a flexible witness. -/
theorem existsFlex_intro (p : Formula Value (Γ.bindFlex a))
    (f : Expr Value Γ (Value a)) (ρ : RigidEnv Value Γ) (σ : Behavior (State Value Γ))
    (h : p.Sat ρ (σ.map fun s => s.extend (f ρ s))) : (Formula.existsFlex a p).Sat ρ σ :=
  Proofs.Logic.Temporal.TLA.Rules.Scoped.existsFlex_intro p f ρ σ h

/-- Semantic E2 (Fig. 9). The conclusion lies in the outer scope, so weakening
it into the premise ensures that it is independent of the bound name. -/
theorem existsFlex_elim {p : Formula Value (Γ.bindFlex a)} {q : Formula Value Γ}
    (h : p.Entails (q.rename (Scope.Rename.weakenFlex Γ a))) :
    (Formula.existsFlex a p).Entails q :=
  Proofs.Logic.Temporal.TLA.Rules.Scoped.existsFlex_elim h

/-- Semantic F1 (Fig. 9). A constant expression may read the rigid environment
and supplies the same value for the entire behavior. -/
theorem existsRigid_intro (p : Formula Value (Γ.bindRigid a))
    (e : RigidEnv Value Γ → Value a) (ρ : RigidEnv Value Γ) (σ : Behavior (State Value Γ))
    (h : p.Sat (ρ.extend (e ρ)) σ) : (Formula.existsRigid a p).Sat ρ σ :=
  ⟨e ρ, h⟩

/-- Semantic F2 (Fig. 9). Weakening the outer conclusion makes it independent
of the new rigid value. -/
theorem existsRigid_elim {p : Formula Value (Γ.bindRigid a)} {q : Formula Value Γ}
    (h : p.Entails (q.rename (Scope.Rename.weakenRigid Γ a))) :
    (Formula.existsRigid a p).Entails q :=
  Proofs.Logic.Temporal.TLA.Rules.Scoped.existsRigid_elim h

end General.Formula
end Silmaril.Logic.Temporal.TLA
