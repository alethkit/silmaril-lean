module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Structured.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Result.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Thms

/-! # Evaluation and separation of mixed trees with structured returns -/

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization (Value)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
  (SumSignature treeNative endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.StructuredProofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {A : Ty α}

private theorem value_lowers {n : Nat} {ss : Fin n → α} (v : Value S ss A) :
    (valueSource (Ψ := Ψ) S v).toLetIter n = some (valueNative S v) := by
  induction v with
  | tree t => exact Mixed.tree_lowers S t
  | unit => rfl
  | pair p q ihp ihq => simp only [valueSource, valueNative, Expr.toLetIter, ihp, ihq,
      Option.map_some, Option.bind_some]
  | inl p ih => simp only [valueSource, valueNative, Expr.toLetIter, ih, Option.map_some]
  | inr q ih => simp only [valueSource, valueNative, Expr.toLetIter, ih, Option.map_some]

public theorem lowers {n : Nat} {ss : Fin n → α} (p : Code S T A ss) :
    p.source.toLetIter n = some p.native := by
  induction p with
  | ret v => exact value_lowers S v
  | atom f args next ih =>
    simp only [Code.source, Code.native, Expr.toLetIter,
      Mixed.tuple_lowers _ _ (fun i => Mixed.tree_lowers S (args i)), ih,
      Option.map_some, Option.bind_some]
  | sum g args left right ihl ihr =>
    simp only [Code.source, Code.native, Expr.toLetIter,
      Mixed.tuple_lowers _ _ (fun i => Mixed.tree_lowers S (args i)), ihl, ihr,
      Option.map_some, Option.bind_some]

section Evaluation

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α} {m : Nat} (modelSlots : Fin m → α)

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "β" => Γ.toBoundCtx
local notation "D" => Ty.denote (Atom S modelSlots)
local notation "M" => SumCall.instructions (ε := ε) S T modelSlots
local notation "free" => (fun x : Empty => x.elim)

omit [HasEff Ψ ε] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem eval_value_exists (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    (v : Value S slots A) (hv : v.Pure (ε := ε) S) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ β (valueNative S v) A,
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote D M free (variableEnv S modelSlots hs vars) =
          ITree.ret (valueDenote S modelSlots vars v) := by
  let instr := endpoints S T
  induction v with
  | tree t => exact Mixed.eval_tree_exists S T modelSlots hs t hv
  | unit => exact ⟨.unit, fun _ => rfl⟩
  | pair p q ihp ihq =>
    obtain ⟨dp, hp⟩ := ihp hv.1
    obtain ⟨dq, hq⟩ := ihq hv.2
    refine ⟨.pair dp dq, fun vars => ?_⟩
    erw [Derivation.denote, hp vars, pure_bind, hq vars, pure_bind]
    rfl
  | inl p ih =>
    obtain ⟨dp, hp⟩ := ih hv
    refine ⟨.inl dp, fun vars => ?_⟩
    erw [Derivation.denote, hp vars, pure_bind]
    rfl
  | inr q ih =>
    obtain ⟨dq, hq⟩ := ih hv
    refine ⟨.inr dq, fun vars => ?_⟩
    erw [Derivation.denote, hq vars, pure_bind]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem eval_aux {n : Nat} {ss : Fin n → α} (e : ε)
    (p : Code S T A ss) (hp : p.WellTyped S T e) :
    letI := endpoints S T
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n)
      (hs : ∀ i : Fin Γ.length, (Γ.get i).1 = .base (ss (i.cast hlen))),
      ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ Γ.toBoundCtx (hlen.symm ▸ p.native) A,
        ∀ vars : (i : Fin n) → Tree S modelSlots (ss i),
          d.denote D M free (variableEnv S modelSlots hs (fun i => vars (i.cast hlen))) =
            p.denote S T modelSlots vars := by
  let instr := endpoints S T
  induction p with
  | @ret n ss v =>
    intro Γ hlen hs
    subst n
    exact eval_value_exists S T modelSlots hs v hp
  | @atom n ss f args next ih =>
    intro Γ hlen hs
    subst n
    have ht := Mixed.slots_extended (a := S.out f) hs
    obtain ⟨d, hd⟩ := Mixed.eval_args_exists S T modelSlots hs args hp.1
    obtain ⟨d', hd'⟩ := ih hp.2.2.2 (Γ := (.base (S.out f), (⊥ : ε)) :: Γ) rfl ht
    refine ⟨.let₁ (.op (f := (Sum.inl f : Φ ⊕ Ψ)) d) d', fun vars => ?_⟩
    erw [Derivation.denote, Derivation.denote, hd vars, pure_bind,
      Mixed.eval_atom_visible S T modelSlots f _ hp.2.1, ITree.vis_bind]
    simp only [Code.denote]
    congr 1
    funext r
    erw [pure_bind]
    let vals := extendValues S modelSlots r vars
    have he := variableEnv_snoc S modelSlots hs ht vals
    exact (congrArg (d'.denote D M free) he).trans (hd' vals)
  | @sum n ss g args left right ihl ihr =>
    intro Γ hlen hs
    subst n
    have hL := Mixed.slots_extended (a := T.left g) hs
    have hR := Mixed.slots_extended (a := T.right g) hs
    obtain ⟨d, hd⟩ := Mixed.eval_args_exists S T modelSlots hs args hp.1
    obtain ⟨dl, hl⟩ := ihl hp.2.2.1 (Γ := (.base (T.left g), (⊥ : ε)) :: Γ) rfl hL
    obtain ⟨dr, hr⟩ := ihr hp.2.2.2 (Γ := (.base (T.right g), (⊥ : ε)) :: Γ) rfl hR
    refine ⟨.case (.op (f := (Sum.inr g : Φ ⊕ Ψ)) d) dl dr, fun vars => ?_⟩
    erw [Derivation.denote, Derivation.denote, hd vars, pure_bind,
      Mixed.eval_sum_request S T modelSlots g, ITree.vis_bind]
    simp only [Code.denote]
    congr 1
    funext r
    erw [pure_bind]
    cases r with
    | inl a =>
      let vals := extendValues S modelSlots a vars
      have he := variableEnv_snoc S modelSlots hs hL vals
      exact (congrArg (dl.denote D M free) he).trans (hl vals)
    | inr b =>
      let vals := extendValues S modelSlots b vars
      have he := variableEnv_snoc S modelSlots hs hR vals
      exact (congrArg (dr.denote D M free) he).trans (hr vals)

public theorem eval_exists (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Code S T A slots) (hp : p.WellTyped S T e) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ β p.native A,
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote D M free (variableEnv S modelSlots hs vars) = p.denote S T modelSlots vars :=
  eval_aux S T modelSlots e p hp rfl hs

end Evaluation

public theorem valueDenote_injective {n : Nat} {ss : Fin n → α} :
    Function.Injective (valueDenote S ss Tree.var (A := A)) := by
  apply Value.denoteWith_injective
  intro a x y h
  simpa only [SingleCall.interpret_vars] using congrArg ULift.down h

public theorem eq_of_denote_eq {n : Nat} {ss : Fin n → α} {p q : Code S T A ss}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (ss i)),
      Code.denote S T modelSlots p vars = Code.denote S T modelSlots q vars) :
    p = q := by
  induction p with
  | @ret size ambient p =>
    cases q with
    | ret q =>
      exact congrArg Code.ret (valueDenote_injective S (ITree.ret_inj.mp (h ambient Tree.var)))
    | atom f args next => exact (ITree.ret_ne_vis _ _ _ (h ambient Tree.var)).elim
    | sum g args left right => exact (ITree.ret_ne_vis _ _ _ (h ambient Tree.var)).elim
  | @atom size ambient f args next ih =>
    cases q with
    | ret q => exact (ITree.ret_ne_vis _ _ _ (h ambient Tree.var).symm).elim
    | sum g req left right =>
      have hh := congrArg (SumCall.headRequest S T ambient) (h ambient Tree.var)
      simp [SumCall.headRequest, Code.denote, ITree.out_vis] at hh
    | atom f' args' next' =>
      have hh := congrArg (SumCall.headRequest S T ambient) (h ambient Tree.var)
      simp only [SumCall.headRequest, Code.denote, ITree.out_vis, Part.map_some, Part.some_inj,
        Option.some.injEq, Sum.inl.injEq, SingleCall.interpret_vars] at hh
      have hf : f = f' := congrArg Sigma.fst hh
      subst f'
      have he : args = args' := eq_of_heq (Sigma.mk.inj hh).2
      subst args'
      congr 1
      apply ih
      intro m ms vars
      let rest := fun i : Fin size => vars i.succ
      have he := congrFun ((ITree.vis_inj (SumCall.Event.atom f (fun i =>
        (args i).interpret S (Tree S ms) Tree.op rest)) _ _).mp (h ms rest)) (vars 0)
      exact (congrArg (fun vals => Code.denote S T ms next vals =
        Code.denote S T ms next' vals) (extendValues_head S vars)).mp he
  | @sum size ambient g args left right ihl ihr =>
    cases q with
    | ret q => exact (ITree.ret_ne_vis _ _ _ (h ambient Tree.var).symm).elim
    | atom f req next =>
      have hh := congrArg (SumCall.headRequest S T ambient) (h ambient Tree.var)
      simp [SumCall.headRequest, Code.denote, ITree.out_vis] at hh
    | sum g' args' left' right' =>
      have hh := congrArg (SumCall.headRequest S T ambient) (h ambient Tree.var)
      simp only [SumCall.headRequest, Code.denote, ITree.out_vis, Part.map_some, Part.some_inj,
        Option.some.injEq, Sum.inr.injEq, SingleCall.interpret_vars] at hh
      have hg : g = g' := congrArg Sigma.fst hh
      subst g'
      have he : args = args' := eq_of_heq (Sigma.mk.inj hh).2
      subst args'
      congr 1
      · apply ihl
        intro m ms vars
        let rest := fun i : Fin size => vars i.succ
        have he := congrFun ((ITree.vis_inj (SumCall.Event.sum g (fun i =>
          (args i).interpret S (Tree S ms) Tree.op rest)) _ _).mp (h ms rest)) (Sum.inl (vars 0))
        exact (congrArg (fun vals => Code.denote S T ms left vals =
          Code.denote S T ms left' vals) (extendValues_head S vars)).mp he
      · apply ihr
        intro m ms vars
        let rest := fun i : Fin size => vars i.succ
        have he := congrFun ((ITree.vis_inj (SumCall.Event.sum g (fun i =>
          (args i).interpret S (Tree S ms) Tree.op rest)) _ _).mp (h ms rest)) (Sum.inr (vars 0))
        exact (congrArg (fun vals => Code.denote S T ms right vals =
          Code.denote S T ms right' vals) (extendValues_head S vars)).mp he


variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  [DecidableEq α] {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

public theorem native_eq_implies_eq (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Code S T A slots) (hp : p.WellTyped S T e) (hq : q.WellTyped S T e)
    (hn : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
      AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx p.native q.native A) : p = q := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  apply eq_of_denote_eq S T
  intro m modelSlots vars
  obtain ⟨dp, hdp⟩ := eval_exists S T modelSlots hs e p hp
  obtain ⟨dq, hdq⟩ := eval_exists S T modelSlots hs e q hq
  have he := LetIter.Semantics.Categorical.denote_eq_of_abortEquiv_nil.{u, u + 2, u, r} (Atom S modelSlots)
    (SumCall.instructions (ε := ε) S T modelSlots) (Mixed.instructions_respectsPure S T modelSlots visible) hn dp dq
    (variableEnv S modelSlots hs vars)
  exact (hdp vars).symm.trans (he.trans (hdq vars))

variable [EffectIteration ε]

public theorem endpoint_reflection_structured {a b : Expr (Φ ⊕ Ψ)}
    (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a A e)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ b A e)
    {t s : Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hu : b.toLetIter Γ.length = some s) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s A ↔ Eqv Γ A e a b := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  refine ⟨fun hn => ?_, fun he => he.toLetIter ht hu⟩
  obtain ⟨p, hp, hpa⟩ := Written.normalize S T hΓ hs e ha
  obtain ⟨q, hq, hqb⟩ := Written.normalize S T hΓ hs e hb
  have hnp := hpa.toLetIter ht (lowers S T p)
  have hnq := hqb.toLetIter hu (lowers S T q)
  have he := native_eq_implies_eq S T visible hs e p q hp hq (hnp.symm.trans (hn.trans hnq))
  subst q
  exact hpa.trans hqb.symm

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.StructuredProofs
