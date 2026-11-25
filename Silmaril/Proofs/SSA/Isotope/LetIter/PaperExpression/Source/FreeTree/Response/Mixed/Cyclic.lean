module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Cyclic.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.VisibleDepth.Thms

/-! # Unbounded observations of repeat-on-right native iteration -/

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
  (SumSignature SumArgs SumResponse endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.CyclicProofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {g : Ψ} {n m : Nat} {β : BoundCtx (Ty α) n} (modelSlots : Fin m → α)

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "D" => Ty.denote (Atom S modelSlots)
local notation "E" => SumCall.Event S T modelSlots
local notation "F" => (Φ ⊕ Ψ)

private theorem input_zero {k : Nat} (args : Fin k → α) (h : k = 0) :
    input k args = .unit := by
  subst k
  rfl

private def castUnit {A : Ty α} (h : Ty.unit = A) :
    letI := endpoints S T
    Derivation F Γ₀ β (.unit : Tm Empty F n) A := by
  letI := endpoints S T
  exact h ▸ Derivation.unit

private def requestUnit (h : T.arity g = 0) :
    letI := endpoints S T
    Derivation F Γ₀ β (.unit : Tm Empty F n) (input (T.arity g) (T.arg g)) :=
  castUnit S T (input_zero (T.arg g) h).symm

private def loopDerivation (h : T.arity g = 0) :
    letI := endpoints S T
    Derivation F Γ₀ β (repeatOnRight (Φ := Φ) g n) (.base (T.left g)) := by
  letI := endpoints S T
  exact .iter (A := Ty.unit) .unit
    (.case (A := .base (T.left g)) (B := .base (T.right g))
      (.op (f := Sum.inr g) (requestUnit S T h)) (.inl .bv) (.inr .unit))

section Denotation

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

local notation "M" => SumCall.instructions (ε := ε) S T modelSlots
local notation "emptyEnv" => (fun x : Empty => x.elim)

private theorem denote_cast_unit {A : Ty α} (h : Ty.unit = A) (ρ : BoundEnv D β) :
    letI := endpoints S T
    (castUnit S T h).denote D M emptyEnv ρ = ITree.ret (cast (congrArg D h) PUnit.unit) := by
  cases h
  rfl

private def nullaryArgs (h : T.arity g = 0) : SumArgs S T modelSlots g :=
  fun i => (i.cast h).elim0

private theorem unpack_nullary (h : T.arity g = 0) (x : D (input (T.arity g) (T.arg g))) :
    unpackArgs S modelSlots (T.arity g) (T.arg g) x = nullaryArgs S T modelSlots h := by
  funext i
  exact (i.cast h).elim0

/-- The body of the iterator has one visible observation and returns a
control sum. The left payload is the result and the right payload is ignored. -/
private def stepTree (h : T.arity g = 0) (_ : D Ty.unit) :
    ITree.Tree E (Atom S modelSlots (T.left g) ⊕ D Ty.unit) :=
  ITree.vis (.sum g (nullaryArgs S T modelSlots h))
    (Sum.elim (fun l => ITree.ret (.inl ⟨l⟩)) (fun _ => ITree.ret (.inr PUnit.unit)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem denote_loop (h : T.arity g = 0) (ρ : BoundEnv D β) :
    letI := endpoints S T
    (loopDerivation S T h).denote D M emptyEnv ρ =
      Silmaril.Elgot.iter (stepTree S T modelSlots h) PUnit.unit := by
  let instr := endpoints S T
  unfold loopDerivation
  erw [Derivation.denote]
  simp only [Derivation.denote]
  have hunit (state : D Ty.unit) := denote_cast_unit (ε := ε) S T modelSlots
    (input_zero (T.arg g) h).symm (ρ.snoc state)
  simp only [requestUnit, hunit]
  simp only [pure_bind, SumCall.instructions, unpack_nullary S T modelSlots h]
  congr 1
  funext state
  erw [pure_bind]
  rw [ITree.vis_bind, ITree.vis_bind]
  change ITree.vis _ _ = stepTree S T modelSlots h state
  rw [stepTree]
  congr 1
  funext reply
  erw [pure_bind]
  cases reply <;> erw [pure_bind] <;> rfl

public theorem repeatOnRight_visible_step (h : T.arity g = 0) (ρ : BoundEnv D β) :
    letI := endpoints S T
    ∃ (d : Derivation F Γ₀ β (repeatOnRight g n) (.base (T.left g))) (args : SumArgs S T modelSlots g),
      let t := d.denote D M emptyEnv ρ
      t = ITree.vis (.sum g args) (Sum.elim (fun l => ITree.ret ⟨l⟩) (fun _ => t)) := by
  let instr := endpoints S T
  refine ⟨loopDerivation S T h, nullaryArgs S T modelSlots h, ?_⟩
  dsimp only
  rw [denote_loop (ε := ε) S T modelSlots h ρ]
  nth_rw 1 [congrFun (ITree.iterate_fixpoint (stepTree S T modelSlots h)) PUnit.unit]
  change (ITree.vis _ _ >>= _) = _
  rw [ITree.vis_bind]
  congr 1
  funext reply
  cases reply <;> erw [pure_bind] <;> rfl

private theorem prefix_loop (h : T.arity g = 0) (ρ : BoundEnv D β) (right : Tree S modelSlots (T.right g)) :
    letI := endpoints S T
    ∀ k, ITree.HasVisiblePrefix k ((loopDerivation S T h).denote D M emptyEnv ρ) := by
  let instr := endpoints S T
  rw [denote_loop (ε := ε) S T modelSlots h ρ]
  intro k
  apply ITree.hasVisiblePrefix_iter
  intro state
  exact ⟨SumResponse S T modelSlots g, .sum g (nullaryArgs S T modelSlots h),
    _, .inr right, PUnit.unit, rfl, rfl⟩

public theorem repeatOnRight_hasVisiblePrefixes (h : T.arity g = 0) (ρ : BoundEnv D β)
    (right : Tree S modelSlots (T.right g)) :
    letI := endpoints S T
    ∃ d : Derivation F Γ₀ β (repeatOnRight g n) (.base (T.left g)),
      ∀ k, ITree.HasVisiblePrefix k (d.denote D M emptyEnv ρ) :=
  ⟨loopDerivation S T h, prefix_loop (ε := ε) S T modelSlots h ρ right⟩

end Denotation

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

public theorem repeatOnRight_typed (h : T.arity g = 0) (e : ε)
    (hg : instrEff g ≤ e) (he : IsIterative e) :
    letI := endpoints S T
    letI : HasEff F ε := effects
    HasTypeEffect Γ₀ β (repeatOnRight (Φ := Φ) g n) (.base (T.left g)) e := by
  let instr := endpoints S T
  let eff : HasEff F ε := effects
  have ht := (loopDerivation S T (β := β) h).toHasType
  refine ⟨ht, ?_⟩
  change HasEffect (.iter .unit (.case (.op (.inr g) .unit) (.inl (.bv 0)) (.inr .unit)) : Tm Empty F n) e
  exact HasEffect.iter he bot_le (sup_le (sup_le hg bot_le) (sup_le bot_le bot_le))

local notation "M" => SumCall.instructions (ε := ε) S T modelSlots

variable [DecidableEq α]

omit [EffectIteration ε] in
private theorem not_eq_of_bounded {t : Tm Empty F n} (h : T.arity g = 0)
    (visible : ∀ k : Ψ, ¬ IsPure (⊥ : ε) k) (ρ : BoundEnv D β) (right : Tree S modelSlots (T.right g))
    (d : letI := endpoints S T; Derivation F Γ₀ β t (.base (T.left g))) {b : Nat}
    (hfinite : letI := endpoints S T
      ITree.VisibleDepthLE (d.denote D M (fun x => x.elim) ρ) b) :
    letI := endpoints S T
    letI : HasEff F ε := effects
    ¬ AbortEquiv (⊥ : ε) Γ₀ β (repeatOnRight g n) t (.base (T.left g)) := by
  let instr := endpoints S T
  let eff : HasEff F ε := effects
  intro hn
  have heq := LetIter.Semantics.Categorical.denote_eq_of_abortEquiv_nil.{u, u + 2, u, r}
    (Atom S modelSlots) _ (instructions_respectsPure S T modelSlots visible) hn (loopDerivation S T h) d ρ
  have hprefix := prefix_loop (ε := ε) S T modelSlots h ρ right (b + 1)
  rw [heq] at hprefix
  exact Nat.not_succ_le_self _ (hfinite _ hprefix)

variable {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

public theorem repeatOnRight_not_raw (h : T.arity g = 0)
    (visible : ∀ k : Ψ, ¬ IsPure (⊥ : ε) k)
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Raw.Program S T (T.left g) slots) (hp : p.WellTyped S T e)
    {t : Tm Empty F Γ.length} (ht : p.source.toLetIter Γ.length = some t) :
    letI := endpoints S T
    letI : HasEff F ε := effects
    ¬ AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (repeatOnRight g Γ.length) t (.base (T.left g)) := by
  let instr := endpoints S T
  let eff : HasEff F ε := effects
  have htyped := (Raw.compile_native S T hΓ hs e p hp ht).1.1
  obtain ⟨dq⟩ := Derivation.ofHasType htyped
  let ms := extendSorts (T.right g) slots
  let vars : (i : Fin Γ.length) → Tree S ms (slots i) := fun i => .var i.succ
  have hfinite := raw_denote_visibleDepth S T visible hΓ hs e p hp ht ms vars dq
  exact not_eq_of_bounded S T ms h visible (variableEnv S ms hs vars) (.var 0) dq hfinite

public theorem repeatOnRight_not_written (h : T.arity g = 0)
    (visible : ∀ k : Ψ, ¬ IsPure (⊥ : ε) k)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε) (p : Expr F)
    (hp : letI := endpoints S T; letI : HasEff F ε := effects; Wf Γ p (.base (T.left g)) e)
    {t : Tm Empty F Γ.length} (ht : p.toLetIter Γ.length = some t) :
    letI := endpoints S T
    letI : HasEff F ε := effects
    ¬ AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (repeatOnRight g Γ.length) t (.base (T.left g)) := by
  let instr := endpoints S T
  let eff : HasEff F ε := effects
  obtain ⟨t', ht', hty⟩ := hp.toLetIter
  have eq : t' = t := Option.some.inj (ht'.symm.trans ht)
  obtain ⟨dq⟩ := Derivation.ofHasType (eq ▸ hty.1)
  let ms := extendSorts (T.right g) slots
  let vars : (i : Fin Γ.length) → Tree S ms (slots i) := fun i => .var i.succ
  obtain ⟨b, hb⟩ := written_denote_bounded (ε := ε) S T ms p ht dq
  exact not_eq_of_bounded S T ms h visible (variableEnv S ms hs vars) (.var 0) dq (hb _)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.CyclicProofs
