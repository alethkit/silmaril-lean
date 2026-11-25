module

public import Silmaril.Logic.Temporal.TLA.General.Defs
public import Silmaril.Logic.Temporal.TLA.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.General.Semantics

public section

namespace Silmaril.Logic.Temporal.TLA.General

universe u v w

variable {Sorts : Type u} {Value : Sorts → Type u}
  {Γ Δ Ξ Ω : Scope Sorts} {C D E : Context Sorts}

namespace Context.Rename

theorem injective_id (C : Context Sorts) : (id C).Injective :=
  fun _ _ _ h => h

theorem Injective.comp {f : Context.Rename C D} {g : Context.Rename D E}
    (hf : f.Injective) (hg : g.Injective) : (f.comp g).Injective :=
  fun s _ _ h => hf s (hg s h)

theorem Injective.under {f : Context.Rename C D} (hf : f.Injective) (a : Sorts) :
    (f.under a).Injective :=
  Proofs.Logic.Temporal.TLA.General.under_injective hf a

end Context.Rename

namespace Scope.Rename

theorem id_comp (f : Scope.Rename Γ Δ) : (id Γ).comp f = f := rfl
theorem comp_id (f : Scope.Rename Γ Δ) : f.comp (id Δ) = f := rfl

theorem comp_assoc (f : Scope.Rename Γ Δ) (g : Scope.Rename Δ Ξ) (h : Scope.Rename Ξ Ω) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

end Scope.Rename

namespace Valuation

theorem extend_drop_last {a : Sorts} (v : Valuation Value (C.bind a)) :
    v.drop.extend v.last = v :=
  Proofs.Logic.Temporal.TLA.General.extend_drop_last v

theorem extend_restrict_under (f : Context.Rename C D) (v : Valuation Value D)
    {a : Sorts} (w : Value a) :
    (v.extend w).restrict (f.under a) = (v.restrict f).extend w :=
  Proofs.Logic.Temporal.TLA.General.extend_restrict_under f v w

/-- Lift any restricted valuation, using `base` to supply otherwise unassigned
coordinates. The current state can serve as the base when lifting a successor. -/
theorem restrict_surjective {f : Context.Rename C D} (hf : f.Injective)
    (base : Valuation Value D) (v : Valuation Value C) :
    ∃ w : Valuation Value D, w.restrict f = v :=
  Proofs.Logic.Temporal.TLA.General.restrict_surjective hf base v

end Valuation

namespace Model

theorem reduct_id (M : Model Value Γ) : M.reduct (Scope.Rename.id Γ) = M := rfl

theorem reduct_comp (M : Model Value Ξ) (f : Scope.Rename Γ Δ) (g : Scope.Rename Δ Ξ) :
    M.reduct (f.comp g) = (M.reduct g).reduct f := rfl

end Model

namespace Action

theorem enabled_rename (f : Scope.Rename Γ Δ) (hf : f.flex.Injective)
    (A : Action Value Γ) (ρ : RigidEnv Value Δ) (s : State Value Δ) :
    (A.rename f ρ).enabled s ↔ (A (ρ.restrict f.rigid)).enabled (s.restrict f.flex) :=
  Proofs.Logic.Temporal.TLA.General.enabled_rename f hf A ρ s

theorem existsRigid_rename {a : Sorts} (A : Action Value (Γ.bindRigid a))
    (f : Scope.Rename Γ Δ) :
    A.existsRigid.rename f = (A.rename (f.underRigid a)).existsRigid :=
  Proofs.Logic.Temporal.TLA.General.action_existsRigid_rename A f

end Action

namespace StatePred

theorem rename_id (p : StatePred Value Γ) : p.rename (Scope.Rename.id Γ) = p :=
  Proofs.Logic.Temporal.TLA.General.statePred_rename_id p

theorem rename_comp (p : StatePred Value Γ) (f : Scope.Rename Γ Δ) (g : Scope.Rename Δ Ξ) :
    p.rename (f.comp g) = (p.rename f).rename g :=
  Proofs.Logic.Temporal.TLA.General.statePred_rename_comp p f g

theorem eval_rename (p : StatePred Value Γ) (f : Scope.Rename Γ Δ) (hf : f.flex.Injective)
    (ρ : RigidEnv Value Δ) (s : State Value Δ) :
    (p.rename f).eval ρ s ↔ p.eval (ρ.restrict f.rigid) (s.restrict f.flex) :=
  Proofs.Logic.Temporal.TLA.General.eval_rename p f hf ρ s

end StatePred

namespace Formula

theorem rename_id (p : Formula Value Γ) : p.rename (Scope.Rename.id Γ) = p :=
  Proofs.Logic.Temporal.TLA.General.formula_rename_id p

theorem rename_comp (p : Formula Value Γ) (f : Scope.Rename Γ Δ) (g : Scope.Rename Δ Ξ) :
    p.rename (f.comp g) = (p.rename f).rename g :=
  Proofs.Logic.Temporal.TLA.General.formula_rename_comp p f g

theorem sat_stutterInvariant (p : Formula Value Γ) (ρ : RigidEnv Value Γ) :
    StutterInvariant (p.Sat ρ) :=
  Proofs.Logic.Temporal.TLA.General.sat_stutterInvariant p ρ

theorem holds_retime (p : Formula Value Γ) (ρ : RigidEnv Value Γ)
    (σ : Behavior (State Value Γ)) (r : Retiming) (n : Nat) :
    p.Holds ρ (σ.retime r) n ↔ p.Holds ρ σ (r.index n) :=
  p.sat_stutterInvariant ρ (StutterEquiv.suffix_retime σ r n)

theorem sat_rename (p : Formula Value Γ) (f : Scope.Rename Γ Δ) (hf : f.flex.Injective)
    (ρ : RigidEnv Value Δ) (σ : Behavior (State Value Δ)) :
    (p.rename f).Sat ρ σ ↔ p.Sat (ρ.restrict f.rigid) (σ.map (Valuation.restrict f.flex)) :=
  Proofs.Logic.Temporal.TLA.General.sat_rename p f hf ρ σ

theorem holds_rename (p : Formula Value Γ) (f : Scope.Rename Γ Δ) (hf : f.flex.Injective)
    (ρ : RigidEnv Value Δ) (σ : Behavior (State Value Δ)) (n : Nat) :
    (p.rename f).Holds ρ σ n ↔
      p.Holds (ρ.restrict f.rigid) (σ.map (Valuation.restrict f.flex)) n :=
  p.sat_rename f hf ρ (σ.suffix n)

/-- Satisfaction commutes with translating a sentence and taking a model
reduct. Only the flexible part of the scope map needs to be injective. -/
theorem satisfies_rename (p : Formula Value Γ) (f : Scope.Rename Γ Δ) (hf : f.flex.Injective)
    (M : Model Value Δ) : (p.rename f).Satisfies M ↔ p.Satisfies (M.reduct f) :=
  p.sat_rename f hf M.rigid M.behavior

/-- In valuation coordinates, a flexible witness is an extended behavior whose
old variables follow the original behavior up to stuttering. -/
theorem sat_existsFlex {a : Sorts} (p : Formula Value (Γ.bindFlex a))
    (ρ : RigidEnv Value Γ) (σ : Behavior (State Value Γ)) :
    (Formula.existsFlex a p).Sat ρ σ ↔
      ∃ τ : Behavior (State Value (Γ.bindFlex a)),
        StutterEquiv σ (τ.map Valuation.drop) ∧ p.Sat ρ τ :=
  Proofs.Logic.Temporal.TLA.General.sat_existsFlex p ρ σ

theorem sat_forallFlex {a : Sorts} (p : Formula Value (Γ.bindFlex a))
    (ρ : RigidEnv Value Γ) (σ : Behavior (State Value Γ)) :
    (p.forallFlex a).Sat ρ σ ↔ ∀ τ : Behavior (State Value (Γ.bindFlex a)),
      StutterEquiv σ (τ.map Valuation.drop) → p.Sat ρ τ := by
  classical
  change (¬ (Formula.existsFlex a (.neg p)).Sat ρ σ) ↔ _
  rw [sat_existsFlex (.neg p) ρ σ]
  simp only [not_exists, not_and, Sat, Classical.not_not]

theorem sat_eventually (p : Formula Value Γ) (ρ : RigidEnv Value Γ)
    (σ : Behavior (State Value Γ)) :
    p.eventually.Sat ρ σ ↔ ∃ n, p.Holds ρ σ n := by
  classical
  simp only [eventually, Sat, Holds, Classical.not_forall, Classical.not_not]

theorem sat_forallRigid {a : Sorts} (p : Formula Value (Γ.bindRigid a))
    (ρ : RigidEnv Value Γ) (σ : Behavior (State Value Γ)) :
    (p.forallRigid a).Sat ρ σ ↔ ∀ v : Value a, p.Sat (ρ.extend v) σ := by
  classical
  simp only [forallRigid, Sat, not_exists, Classical.not_not]

end Formula

theorem Refines.comp {S : Type u} {T : Type v} {U : Type w} {p : Behavior S → Prop} {q : Behavior T → Prop}
    {r : Behavior U → Prop} {f : S → T} {g : T → U}
    (h : Refines p f q) (h' : Refines q g r) : Refines p (g ∘ f) r :=
  fun σ hσ => h' (σ.map f) (h σ hσ)

end Silmaril.Logic.Temporal.TLA.General
