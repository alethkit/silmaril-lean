module

public import Silmaril.Logic.Temporal.TLA.Rules.Defs
public import Silmaril.Logic.Temporal.TLA.General.Thms

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA.Rules

open Silmaril.Logic.Temporal.TLA

universe u v w x

theorem hide_extension_iff {S : Type u} {H : Type v} {p : Behavior S → Prop}
    {q : Behavior (S × H) → Prop} (invariant : StutterInvariant p)
    (sound : General.Refines q Prod.fst p)
    (lift : ∀ σ, p σ → ∃ τ, τ.map Prod.fst = σ ∧ q τ)
    (σ : Behavior S) : hide q σ ↔ p σ := by
  constructor
  · rintro ⟨τ, same, hτ⟩
    exact (invariant same).mpr (sound τ hτ)
  · intro hσ
    obtain ⟨τ, same, hτ⟩ := lift σ hσ
    exact ⟨τ, same ▸ StutterEquiv.refl σ, hτ⟩

theorem hide_refines {S : Type u} {H : Type v} {T : Type w} {K : Type x}
    {p : Behavior (S × H) → Prop} {q : Behavior (T × K) → Prop}
    {f : S → T} {g : S × H → K}
    (sim : General.Refines p (fun s => (f s.1, g s)) q) :
    General.Refines (hide p) f (hide q) := by
  intro σ hσ
  obtain ⟨τ, same, hτ⟩ := hσ
  refine ⟨τ.map (fun s => (f s.1, g s)), ?_, sim τ hτ⟩
  change StutterEquiv (σ.map f) ((τ.map Prod.fst).map f)
  exact same.map f

theorem enabled_pullback_iff {S : Type u} {T : Type v} (f : S → T)
    (A : Action T) (s : S) (lift : ∀ t, A (f s) t → ∃ s', f s' = t) :
    (Action.enabled fun x y => A (f x) (f y)) s ↔ A.enabled (f s) := by
  constructor
  · rintro ⟨s', hs'⟩
    exact ⟨f s', hs'⟩
  · rintro ⟨t, ht⟩
    obtain ⟨s', rfl⟩ := lift t ht
    exact ⟨s', ht⟩

namespace Scoped

open Silmaril.Logic.Temporal.TLA.General

variable {Sorts : Type u} {Value : Sorts → Type u} {Γ : Scope Sorts} {a : Sorts}

theorem existsFlex_intro (p : General.Formula Value (Γ.bindFlex a))
    (f : Expr Value Γ (Value a)) (ρ : RigidEnv Value Γ) (σ : Behavior (State Value Γ))
    (h : p.Sat ρ (σ.map fun s => s.extend (f ρ s))) :
    (General.Formula.existsFlex a p).Sat ρ σ := by
  apply (p.sat_existsFlex ρ σ).mpr
  refine ⟨σ.map (fun s => s.extend (f ρ s)), ?_, h⟩
  change StutterEquiv σ σ
  exact StutterEquiv.refl σ

theorem existsFlex_elim {p : General.Formula Value (Γ.bindFlex a)}
    {q : General.Formula Value Γ}
    (h : p.Entails (q.rename (Scope.Rename.weakenFlex Γ a))) :
    (General.Formula.existsFlex a p).Entails q := by
  intro m hm
  obtain ⟨τ, same, hp⟩ := (p.sat_existsFlex m.rigid m.behavior).mp hm
  have injective : (Scope.Rename.weakenFlex Γ a).flex.Injective :=
    fun _ _ _ eq => Sum.inl.inj eq
  exact (q.sat_stutterInvariant m.rigid same).mpr
    ((q.sat_rename _ injective m.rigid τ).mp (h ⟨m.rigid, τ⟩ hp))

theorem existsRigid_elim {p : General.Formula Value (Γ.bindRigid a)}
    {q : General.Formula Value Γ}
    (h : p.Entails (q.rename (Scope.Rename.weakenRigid Γ a))) :
    (General.Formula.existsRigid a p).Entails q := by
  intro m hm
  obtain ⟨v, hp⟩ := hm
  exact (q.sat_rename _ (Context.Rename.injective_id Γ.flex) _ _).mp
    (h ⟨m.rigid.extend v, m.behavior⟩ hp)

end Scoped
end Silmaril.Proofs.Logic.Temporal.TLA.Rules
