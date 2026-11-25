module

public import Silmaril.Logic.Temporal.TLA.General.Defs
public import Silmaril.Logic.Temporal.TLA.Thms

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA.General

open Silmaril.Logic.Temporal.TLA (Behavior Retiming StutterEquiv StutterInvariant hide hide_map_iff
  hide_stutterInvariant)
open Silmaril.Logic.Temporal.TLA.General

universe u

variable {Sorts : Type u} {Value : Sorts → Type u}
  {Γ Δ Ξ : Scope Sorts} {C D E : Context Sorts}

theorem under_injective {f : Context.Rename C D} (hf : f.Injective) (a : Sorts) :
    (f.under a).Injective := by
  intro s x y h
  cases x <;> cases y
  · exact congrArg Sum.inl (hf s (Sum.inl.inj h))
  · cases h
  · cases h
  · congr

theorem under_id (C : Context Sorts) (a : Sorts) :
    (Context.Rename.id C).under a = Context.Rename.id (C.bind a) := by
  funext s x
  cases x <;> rfl

theorem under_comp (f : Context.Rename C D) (g : Context.Rename D E) (a : Sorts) :
    (f.comp g).under a = (f.under a).comp (g.under a) := by
  funext s x
  cases x <;> rfl

theorem extend_drop_last {a : Sorts} (v : Valuation Value (C.bind a)) :
    v.drop.extend v.last = v := by
  funext s x
  cases x with
  | inl => rfl
  | inr e =>
    cases e with
    | up eq => cases eq; rfl

theorem extend_restrict_under (f : Context.Rename C D) (v : Valuation Value D)
    {a : Sorts} (w : Value a) :
    (v.extend w).restrict (f.under a) = (v.restrict f).extend w := by
  funext s x
  cases x <;> rfl

theorem restrict_surjective {f : Context.Rename C D} (hf : f.Injective)
    (base : Valuation Value D) (v : Valuation Value C) :
    ∃ w : Valuation Value D, w.restrict f = v := by
  classical
  let w : Valuation Value D := fun s y =>
    if h : ∃ x, f s x = y then v s (Classical.choose h) else base s y
  refine ⟨w, ?_⟩
  funext s x
  change (if h : ∃ x', f s x' = f s x then v s (Classical.choose h) else base s (f s x)) =
    v s x
  rw [dite_eq_left ⟨x, rfl⟩]
  exact congrArg (v s) (hf s (Classical.choose_spec (⟨x, rfl⟩ : ∃ x', f s x' = f s x)))

theorem enabled_rename (f : Scope.Rename Γ Δ) (hf : f.flex.Injective)
    (A : Action Value Γ) (ρ : RigidEnv Value Δ) (s : State Value Δ) :
    (A.rename f ρ).enabled s ↔ (A (ρ.restrict f.rigid)).enabled (s.restrict f.flex) := by
  constructor
  · rintro ⟨t, step⟩
    exact ⟨t.restrict f.flex, step⟩
  · rintro ⟨t, step⟩
    obtain ⟨lifted, hlifted⟩ := restrict_surjective hf s t
    refine ⟨lifted, ?_⟩
    change A (ρ.restrict f.rigid) (s.restrict f.flex) (lifted.restrict f.flex)
    rwa [hlifted]

theorem action_existsRigid_rename {a : Sorts} (A : Action Value (Γ.bindRigid a))
    (f : Scope.Rename Γ Δ) :
    A.existsRigid.rename f = (A.rename (f.underRigid a)).existsRigid := by
  funext ρ s t
  apply propext
  apply exists_congr
  intro v
  change A ((ρ.restrict f.rigid).extend v) (s.restrict f.flex) (t.restrict f.flex) ↔
    A ((ρ.extend v).restrict (f.rigid.under a)) (s.restrict f.flex) (t.restrict f.flex)
  rw [extend_restrict_under]

private theorem underRigid_id (Γ : Scope Sorts) (a : Sorts) :
    (Scope.Rename.id Γ).underRigid a = Scope.Rename.id (Γ.bindRigid a) := by
  simp only [Scope.Rename.id, Scope.Rename.underRigid, under_id]

private theorem underFlex_id (Γ : Scope Sorts) (a : Sorts) :
    (Scope.Rename.id Γ).underFlex a = Scope.Rename.id (Γ.bindFlex a) := by
  simp only [Scope.Rename.id, Scope.Rename.underFlex, under_id]

private theorem underRigid_comp (f : Scope.Rename Γ Δ) (g : Scope.Rename Δ Ξ) (a : Sorts) :
    (f.comp g).underRigid a = (f.underRigid a).comp (g.underRigid a) := by
  simp only [Scope.Rename.comp, Scope.Rename.underRigid, under_comp]

private theorem underFlex_comp (f : Scope.Rename Γ Δ) (g : Scope.Rename Δ Ξ) (a : Sorts) :
    (f.comp g).underFlex a = (f.underFlex a).comp (g.underFlex a) := by
  simp only [Scope.Rename.comp, Scope.Rename.underFlex, under_comp]

theorem statePred_rename_id (p : StatePred Value Γ) : p.rename (Scope.Rename.id Γ) = p := by
  induction p with
  | atom | enabled => rfl
  | neg _ ih => simp only [StatePred.rename, ih]
  | conj _ _ ihp ihq => simp only [StatePred.rename, ihp, ihq]
  | existsRigid _ _ ih => simp only [StatePred.rename, underRigid_id, ih]

theorem statePred_rename_comp (p : StatePred Value Γ) (f : Scope.Rename Γ Δ)
    (g : Scope.Rename Δ Ξ) : p.rename (f.comp g) = (p.rename f).rename g := by
  induction p generalizing Δ Ξ with
  | atom | enabled => rfl
  | neg _ ih => simp only [StatePred.rename, ih]
  | conj _ _ ihp ihq => simp only [StatePred.rename, ihp, ihq]
  | existsRigid _ _ ih => simp only [StatePred.rename, underRigid_comp, ih]

theorem formula_rename_id (p : Formula Value Γ) : p.rename (Scope.Rename.id Γ) = p := by
  induction p with
  | state p => simp only [Formula.rename, statePred_rename_id]
  | alwaysBracket => rfl
  | neg _ ih | always _ ih => simp only [Formula.rename, ih]
  | conj _ _ ihp ihq => simp only [Formula.rename, ihp, ihq]
  | existsRigid _ _ ih => simp only [Formula.rename, underRigid_id, ih]
  | existsFlex _ _ ih => simp only [Formula.rename, underFlex_id, ih]

theorem formula_rename_comp (p : Formula Value Γ) (f : Scope.Rename Γ Δ)
    (g : Scope.Rename Δ Ξ) : p.rename (f.comp g) = (p.rename f).rename g := by
  induction p generalizing Δ Ξ with
  | state p => simp only [Formula.rename, statePred_rename_comp]
  | alwaysBracket => rfl
  | neg _ ih | always _ ih => simp only [Formula.rename, ih]
  | conj _ _ ihp ihq => simp only [Formula.rename, ihp, ihq]
  | existsRigid _ _ ih => simp only [Formula.rename, underRigid_comp, ih]
  | existsFlex _ _ ih => simp only [Formula.rename, underFlex_comp, ih]

theorem eval_rename (p : StatePred Value Γ) (f : Scope.Rename Γ Δ) (hf : f.flex.Injective)
    (ρ : RigidEnv Value Δ) (s : State Value Δ) :
    (p.rename f).eval ρ s ↔ p.eval (ρ.restrict f.rigid) (s.restrict f.flex) := by
  induction p generalizing Δ with
  | atom => rfl
  | enabled A => exact enabled_rename f hf A ρ s
  | neg p ih => exact not_congr (ih f hf ρ s)
  | conj p q ihp ihq => exact and_congr (ihp f hf ρ s) (ihq f hf ρ s)
  | existsRigid a p ih =>
    simp only [StatePred.rename, StatePred.eval]
    exact exists_congr fun v => by
      rw [← extend_restrict_under f.rigid ρ v]
      exact ih (f.underRigid a) hf (ρ.extend v) s

theorem sat_stutterInvariant (p : Formula Value Γ) (ρ : RigidEnv Value Γ) :
    StutterInvariant (p.Sat ρ) := by
  induction p with
  | state p =>
    rintro σ τ ⟨r, t, agrees⟩
    have same : σ 0 = τ 0 := by
      simpa only [Behavior.retime, r.zero, t.zero] using congrFun agrees 0
    simp only [Formula.Sat, same]
  | alwaysBracket A e => exact (Silmaril.Logic.Temporal.TLA.Formula.alwaysBracket (A ρ) (e ρ)).sat_stutterInvariant
  | neg p ih =>
    intro σ τ h
    exact not_congr (ih ρ h)
  | conj p q ihp ihq =>
    intro σ τ h
    exact and_congr (ihp ρ h) (ihq ρ h)
  | always p ih =>
    have expand (σ : Behavior (State Value _)) (r : Retiming) :
        (Formula.always p).Sat ρ (σ.retime r) ↔ (Formula.always p).Sat ρ σ := by
      constructor
      · intro all n
        obtain ⟨k, _, hk, _⟩ := r.crosses (i := 0) (j := n) (by rw [r.zero]; omega)
        have suffix := (ih ρ (StutterEquiv.suffix_retime σ r k)).mp (all k)
        rwa [hk] at suffix
      · intro all k
        exact (ih ρ (StutterEquiv.suffix_retime σ r k)).mpr (all (r.index k))
    rintro σ τ ⟨r, t, agrees⟩
    exact (expand σ r).symm.trans (agrees ▸ expand τ t)
  | existsRigid a p ih =>
    intro σ τ h
    exact exists_congr fun v => ih (ρ.extend v) h
  | existsFlex a p _ => exact hide_stutterInvariant _

theorem sat_rename (p : Formula Value Γ) (f : Scope.Rename Γ Δ) (hf : f.flex.Injective)
    (ρ : RigidEnv Value Δ) (σ : Behavior (State Value Δ)) :
    (p.rename f).Sat ρ σ ↔ p.Sat (ρ.restrict f.rigid) (σ.map (Valuation.restrict f.flex)) := by
  induction p generalizing Δ with
  | state p => exact eval_rename p f hf ρ (σ 0)
  | alwaysBracket => rfl
  | neg p ih => exact not_congr (ih f hf ρ σ)
  | conj p q ihp ihq => exact and_congr (ihp f hf ρ σ) (ihq f hf ρ σ)
  | always p ih => exact forall_congr' fun n => ih f hf ρ (σ.suffix n)
  | existsRigid a p ih =>
    simp only [Formula.rename, Formula.Sat]
    exact exists_congr fun v => by
      rw [← extend_restrict_under f.rigid ρ v]
      exact ih (f.underRigid a) hf (ρ.extend v) σ
  | @existsFlex Γ a p ih =>
    simp only [Formula.rename, Formula.Sat]
    have operandInvariant : StutterInvariant (fun τ : Behavior (State Value Γ × Value a) =>
        p.Sat (ρ.restrict f.rigid) (τ.map fun z => z.1.extend z.2)) := by
      intro τ υ h
      exact sat_stutterInvariant p _ (h.map fun z => z.1.extend z.2)
    rw [← hide_map_iff (Valuation.restrict f.flex) operandInvariant σ]
    apply exists_congr
    intro τ
    apply and_congr_right
    intro _
    have commute :
        (τ.map fun z => z.1.extend z.2).map (Valuation.restrict (f.underFlex a).flex) =
        (τ.map fun z => (z.1.restrict f.flex, z.2)).map (fun z => z.1.extend z.2) := by
      funext i
      exact extend_restrict_under f.flex (τ i).1 (τ i).2
    have body := ih (f.underFlex a) (under_injective hf a) ρ (τ.map fun z => z.1.extend z.2)
    rw [commute] at body
    exact body

theorem sat_existsFlex {a : Sorts} (p : Formula Value (Γ.bindFlex a))
    (ρ : RigidEnv Value Γ) (σ : Behavior (State Value Γ)) :
    (Formula.existsFlex a p).Sat ρ σ ↔
      ∃ τ : Behavior (State Value (Γ.bindFlex a)),
        StutterEquiv σ (τ.map Valuation.drop) ∧ p.Sat ρ τ := by
  constructor
  · rintro ⟨τ, hσ, hp⟩
    refine ⟨τ.map (fun z => z.1.extend z.2), ?_, hp⟩
    exact hσ
  · rintro ⟨τ, hσ, hp⟩
    refine ⟨τ.map (fun v => (v.drop, v.last)), ?_, ?_⟩
    · exact hσ
    change p.Sat ρ ((τ.map _).map _)
    have same : (τ.map (fun v => (v.drop, v.last))).map (fun z => z.1.extend z.2) = τ :=
      funext fun i => extend_drop_last (τ i)
    rwa [same]

end Silmaril.Proofs.Logic.Temporal.TLA.General
