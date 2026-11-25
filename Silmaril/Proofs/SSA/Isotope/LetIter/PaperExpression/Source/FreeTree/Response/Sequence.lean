module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall.Thms

/-! # Reflection for finite sequences by fresh response specialization -/

open Silmaril Silmaril.Isotope Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.Semantics

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Proofs

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {c : α} {n : Nat} {slots : Fin n → α}

public theorem lowers (p : Sequence S c slots) : p.source.toLetIter n = some p.native := by
  induction p with
  | ret p => exact tree_lowers S p
  | call f args next ih =>
    simp only [Sequence.source, Sequence.native, Expr.toLetIter,
      tree_lowers S, ih, Option.bind_some, Option.map_some]

public theorem eq_of_denoteWith_eq
    {E : {m : Nat} → (Fin m → α) → Type (u + 1) → Type (u + 1)}
    (event : ∀ {m} (modelSlots : Fin m → α) (f : Φ),
      Args S modelSlots f → E modelSlots (Tree S modelSlots (S.out f)))
    (label : ∀ {m} (modelSlots : Fin m → α) {X}, E modelSlots X → Option (Request S modelSlots))
    (hlabel : ∀ {m} (modelSlots : Fin m → α) (f : Φ) (args : Args S modelSlots f),
      label modelSlots (event modelSlots f args) = some ⟨f, args⟩)
    {p q : Sequence S c slots}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (slots i)),
      denoteWith S modelSlots (event modelSlots) p vars =
        denoteWith S modelSlots (event modelSlots) q vars) : p = q := by
  induction p with
  | @ret size ambient p =>
    cases q with
    | ret q =>
      have hb := h ambient Tree.var
      have hv := congrArg ULift.down (ITree.ret_inj.mp hb)
      simpa only [SingleCall.interpret_vars] using congrArg (Sequence.ret (S := S)) hv
    | call g args next =>
      exact (ITree.ret_ne_vis _ _ _ (h ambient Tree.var)).elim
  | @call size ambient f args next ih =>
    cases q with
    | ret q => exact (ITree.ret_ne_vis _ _ _ (h ambient Tree.var).symm).elim
    | call g args' next' =>
      have hh := congrArg (fun t => (ITree.out t).map (fun
        | .ret _ => none
        | .vis e _ => label ambient e)) (h ambient Tree.var)
      simp only [denoteWith, ITree.out_vis, Part.map_some, Part.some_inj,
        hlabel, Option.some.injEq, SingleCall.interpret_vars] at hh
      have hfg := congrArg Sigma.fst hh
      change f = g at hfg
      subst g
      have ha : args = args' := eq_of_heq (Sigma.mk.inj hh).2
      subst args'
      congr 1
      apply ih
      intro m modelSlots vars
      let rest := fun i : Fin size => vars i.succ
      have htail := congrFun ((ITree.vis_inj (event modelSlots f (fun i =>
        (args i).interpret S (Tree S modelSlots) Tree.op rest)) _ _).mp (h modelSlots rest)) (vars 0)
      have hv : extendValues S modelSlots (vars 0) rest = vars := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      exact (congrArg (fun vals => denoteWith S modelSlots (event modelSlots) next vals =
        denoteWith S modelSlots (event modelSlots) next' vals) hv).mp htail

private def atomicLabel {m : Nat} (modelSlots : Fin m → α) {X : Type (u + 1)} :
    Event S modelSlots X → Option (Request S modelSlots)
  | .call f args => some ⟨f, args⟩

public theorem eq_of_denote_eq {p q : Sequence S c slots}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (slots i)),
      Sequence.denote S modelSlots p vars = Sequence.denote S modelSlots q vars) : p = q :=
  eq_of_denoteWith_eq S (E := fun slots => Event S slots) (fun _ => Event.call)
    (atomicLabel S) (fun _ _ _ => rfl) h

section Typed

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

private theorem slots_extended {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}
    (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (a : α) :
    ∀ i : Fin (Γ.length + 1),
      (((Ty.base a, (⊥ : ε)) :: Γ).get i).1 = .base (extendSorts a ts i) :=
  fun i => Fin.cases (motive := fun j =>
    (((Ty.base a, (⊥ : ε)) :: Γ).get j).1 = .base (extendSorts a ts j)) rfl hslots i

private theorem pure_extended {Γ : EffectCtx (Ty α) ε} (hΓ : Γ.Pure) (a : α) :
    EffectCtx.Pure ((Ty.base a, (⊥ : ε)) :: Γ) :=
  fun i => Fin.cases (motive := fun j => (((Ty.base a, (⊥ : ε)) :: Γ).get j).2 = ⊥) rfl hΓ i

private theorem wf_aux (e : ε) (p : Sequence S c slots) (hp : Sequence.WellTyped S e p) :
    letI := S.endpoints
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n), Γ.Pure →
      (∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots (i.cast hlen))) →
      Wf Γ p.source (.base c) e := by
  let instr := S.endpoints
  induction p with
  | @ret size ambient p =>
    intro Γ hlen hΓ hslots
    subst size
    exact tree_wf S p hp hΓ hslots e
  | @call size ambient f args next ih =>
    intro Γ hlen hΓ hslots
    subst size
    exact .let₁ (SingleCall.request_wf S args hp.1 hΓ hslots hp.2.2.1)
      (ih hp.2.2.2 rfl (pure_extended hΓ _) (slots_extended hslots _))

public theorem wf {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (p : Sequence S c ts) (hp : Sequence.WellTyped S e p) :
    letI := S.endpoints
    Wf Γ p.source (.base c) e :=
  wf_aux S e p hp rfl hΓ hslots

variable {m : Nat} (modelSlots : Fin m → α)
local notation "D" => Ty.denote (Atom S modelSlots)
local notation "M" => instructions (ε := ε) S modelSlots

private theorem eval_aux (e : ε) (p : Sequence S c slots) (hp : Sequence.WellTyped S e p) :
    letI := S.endpoints
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n)
      (hslots : ∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots (i.cast hlen))),
      ∃ d : Derivation Φ Γ₀ Γ.toBoundCtx (hlen.symm ▸ p.native) (.base c),
        ∀ vars : (i : Fin n) → Tree S modelSlots (slots i),
          d.denote D M (fun x => x.elim)
              (variableEnv S modelSlots hslots (fun i => vars (i.cast hlen))) =
            Sequence.denote S modelSlots p vars := by
  let instr := S.endpoints
  induction p with
  | @ret size ambient p =>
    intro Γ hlen hslots
    subst size
    exact SingleCall.eval_tree_exists S modelSlots p hp hslots
  | @call size ambient f args next ih =>
    intro Γ hlen hslots
    subst size
    let Γ' := (Ty.base (S.out f), (⊥ : ε)) :: Γ
    have ht := slots_extended hslots (S.out f)
    obtain ⟨d, hd⟩ := SingleCall.eval_request_exists S modelSlots args hp.1 hp.2.1 hslots
    obtain ⟨d', hd'⟩ := ih hp.2.2.2 (Γ := Γ') rfl ht
    refine ⟨.let₁ d d', fun vars => ?_⟩
    let ρ := variableEnv S modelSlots hslots vars
    change (d.denote D M (fun x => x.elim) ρ >>= fun r =>
      d'.denote D M (fun x => x.elim) (ρ.snoc r)) = _
    rw [hd vars, ITree.vis_bind]
    simp only [Sequence.denote, Sequence.denoteWith]
    apply (ITree.vis_inj (Event.call f (fun i =>
      (args i).interpret S (Tree S modelSlots) Tree.op vars)) _ _).mpr
    funext r
    erw [pure_bind]
    have hs := variableEnv_snoc S modelSlots hslots ht (extendValues S modelSlots r vars)
    exact (congrArg (d'.denote D M (fun x => x.elim)) hs).trans
      (hd' (extendValues S modelSlots r vars))

public theorem eval_exists {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}
    (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (p : Sequence S c ts) (hp : Sequence.WellTyped S e p) :
    letI := S.endpoints
    ∃ d : Derivation Φ Γ₀ Γ.toBoundCtx p.native (.base c),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (ts i),
        d.denote D M (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
          Sequence.denote S modelSlots p vars :=
  eval_aux S modelSlots e p hp rfl hslots

end Typed

section Reflection

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] [DecidableEq α]

omit [EffectIteration ε] in
public theorem native_eq_implies_eq {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}
    (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (p q : Sequence S c ts) (hp : Sequence.WellTyped S e p) (hq : Sequence.WellTyped S e q)
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native (.base c)) :
    p = q := by
  let instr := S.endpoints
  apply eq_of_denote_eq S
  intro m modelSlots vars
  obtain ⟨dp, hdp⟩ := eval_exists S modelSlots hslots e p hp
  obtain ⟨dq, hdq⟩ := eval_exists S modelSlots hslots e q hq
  have he := native_sound (ε := ε) S modelSlots dp dq (variableEnv S modelSlots hslots vars) hn
  exact (hdp vars).symm.trans (he.trans (hdq vars))

public theorem endpoint_reflection {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (p q : Sequence S c ts) (hp : Sequence.WellTyped S e p) (hq : Sequence.WellTyped S e q) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native (.base c) ↔
      Eqv Γ (.base c) e p.source q.source := by
  let instr := S.endpoints
  refine ⟨fun hn => ?_, fun he => he.toLetIter (lowers S p) (lowers S q)⟩
  have h := native_eq_implies_eq S hslots e p q hp hq hn
  subst q
  exact .refl (wf S hΓ hslots e p hp)

end Reflection

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Proofs
