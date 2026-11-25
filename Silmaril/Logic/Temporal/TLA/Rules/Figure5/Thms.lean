module

public import Silmaril.Logic.Temporal.TLA.Rules.Figure5.Defs
public import Silmaril.Logic.Temporal.TLA.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.Rules.Figure5.Soundness

/-! Semantic soundness of the action and fairness rules of Lamport Fig. 5. -/

public section

namespace Silmaril.Logic.Temporal.TLA.Rules.Figure5

open Formula

universe u

variable {S T V W : Type u}

/-- TLA1. The preservation action can be bracketed when observation-preserving
steps themselves preserve the predicate. -/
theorem tla1 {P : StatePred S} {f : StateExpr S V}
    (preserveUnchanged : ∀ s t, P s → Action.unchanged f s t → P t)
    (σ : Behavior S) :
    (always (state P)).Sat σ ↔
      (conj (state P) (alwaysBracket (fun s t => P s → P t) f)).Sat σ :=
  Proofs.Logic.Temporal.TLA.Rules.Figure5.tla1 preserveUnchanged σ

/-- TLA2. Simulate bracket steps under an always-held source predicate. -/
theorem tla2 {P Q : StatePred S} {A B : Action S} {f : StateExpr S V} {g : StateExpr S W}
    (simulate : ∀ s t, P s → A.bracket f s t → Q s ∧ B.bracket g s t) :
    (conj (always (state P)) (alwaysBracket A f)).Entails
      (conj (always (state Q)) (alwaysBracket B g)) :=
  Proofs.Logic.Temporal.TLA.Rules.Figure5.tla2 simulate

/-- INV1. A predicate preserved by bracket steps holds throughout a behavior
that starts in the predicate and follows those steps. -/
theorem inv1 {I : StatePred S} {N : Action S} {f : StateExpr S V}
    (preserve : ∀ s t, I s → N.bracket f s t → I t) :
    (conj (state I) (alwaysBracket N f)).Entails (always (state I)) :=
  fun σ h => spec_invariant (.state fun _ => True) (fun _ hI => hI) preserve σ ⟨h.1, h.2, trivial⟩

/-- INV2. Under a global invariant, conjoin it at both ends of the next-state action. -/
theorem inv2 {I : StatePred S} {N : Action S} {f : StateExpr S V}
    (σ : Behavior S) (invariant : (always (state I)).Sat σ) :
    (alwaysBracket N f).Sat σ ↔ (alwaysBracket (fun s t => N s t ∧ I s ∧ I t) f).Sat σ :=
  Proofs.Logic.Temporal.TLA.Rules.Figure5.inv2 σ invariant

/-- WF1. Progress need only hold on changing steps in both the next-state action
and the fair action. Enabledness ranges over all successors of the fair angle action. -/
theorem wf1 {P Q : StatePred S} {N A : Action S} {f : StateExpr S V}
    (waiting : ∀ s t, P s → N.bracket f s t → P t ∨ Q t)
    (progress : ∀ s t, P s → Action.angle (fun x y => N x y ∧ A x y) f s t → Q t)
    (enabled : ∀ s, P s → (A.angle f).enabled s) :
    (conj (alwaysBracket N f) (weakFair A f)).Entails ((state P).leadsTo (state Q)) :=
  Proofs.Logic.Temporal.TLA.Rules.Figure5.wf1 waiting progress enabled

/-- SF1. On a tail where P, the step constraint and F hold throughout,
eventual enabledness suffices. The same premise applies to every later suffix. -/
theorem sf1 {P Q : StatePred S} {N A : Action S} {f : StateExpr S V} {F : Formula S}
    (waiting : ∀ s t, P s → N.bracket f s t → P t ∨ Q t)
    (progress : ∀ s t, P s → Action.angle (fun x y => N x y ∧ A x y) f s t → Q t)
    (enabled : (conj (always (state P)) (conj (alwaysBracket N f) (always F))).Entails
      (eventually (state (A.angle f).enabled))) :
    (conj (alwaysBracket N f) (conj (strongFair A f) (always F))).Entails
      ((state P).leadsTo (state Q)) :=
  Proofs.Logic.Temporal.TLA.Rules.Figure5.sf1 waiting progress enabled

/-- WF2. The action M and observation g describe pulled-back steps. Instantiate
enabled with target angle enabledness composed with the refinement map. -/
theorem wf2 {P enabled : StatePred S} {N A B M : Action S}
    {f : StateExpr S V} {g : StateExpr S W} {F : Formula S}
    (simulate : ∀ s t, Action.angle (fun x y => N x y ∧ B x y) f s t → M.angle g s t)
    (progress : ∀ s t, P s → P t →
      Action.angle (fun x y => N x y ∧ A x y) f s t → enabled s → B s t)
    (enableSource : ∀ s, P s → enabled s → (A.angle f).enabled s)
    (stabilize : (conj (alwaysBracket (fun s t => N s t ∧ ¬ B s t) f)
      (conj (weakFair A f) (conj (always F) (eventually (always (state enabled)))))).Entails
      (eventually (always (state P)))) :
    (conj (alwaysBracket N f) (conj (weakFair A f) (always F))).Entails
      (weakFairWithEnabled M g enabled) :=
  Proofs.Logic.Temporal.TLA.Rules.Figure5.wf2 simulate progress enableSource stabilize

/-- SF2. Recurrent target enabledness replaces eventual continuous enabledness,
and the progress premise has no target enabledness guard. -/
theorem sf2 {P enabled : StatePred S} {N A B M : Action S}
    {f : StateExpr S V} {g : StateExpr S W} {F : Formula S}
    (simulate : ∀ s t, Action.angle (fun x y => N x y ∧ B x y) f s t → M.angle g s t)
    (progress : ∀ s t, P s → P t →
      Action.angle (fun x y => N x y ∧ A x y) f s t → B s t)
    (enableSource : ∀ s, P s → enabled s → (A.angle f).enabled s)
    (stabilize : (conj (alwaysBracket (fun s t => N s t ∧ ¬ B s t) f)
      (conj (strongFair A f) (conj (always F) (always (eventually (state enabled)))))).Entails
      (eventually (always (state P)))) :
    (conj (alwaysBracket N f) (conj (strongFair A f) (always F))).Entails
      (strongFairWithEnabled M g enabled) :=
  Proofs.Logic.Temporal.TLA.Rules.Figure5.sf2 simulate progress enableSource stabilize

/-- Weak fairness of the mapped behavior evaluates enabledness in the target. -/
theorem weakFair_map_iff (map : S → T) (M : Action T) (g : StateExpr T W) (σ : Behavior S) :
    (weakFair M g).Sat (σ.map map) ↔
      (weakFairWithEnabled (fun s t => M (map s) (map t)) (g ∘ map)
        ((M.angle g).enabled ∘ map)).Sat σ :=
  Iff.rfl

/-- Strong fairness of the mapped behavior evaluates enabledness in the target. -/
theorem strongFair_map_iff (map : S → T) (M : Action T) (g : StateExpr T W) (σ : Behavior S) :
    (strongFair M g).Sat (σ.map map) ↔
      (strongFairWithEnabled (fun s t => M (map s) (map t)) (g ∘ map)
        ((M.angle g).enabled ∘ map)).Sat σ :=
  Iff.rfl

end Silmaril.Logic.Temporal.TLA.Rules.Figure5
