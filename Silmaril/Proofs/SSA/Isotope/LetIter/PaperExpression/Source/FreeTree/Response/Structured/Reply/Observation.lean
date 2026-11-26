module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Observation.Defs
public import Silmaril.SSA.Isotope.LetIter.Monadic.Substitution.Thms

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation AbortEquiv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape.Proofs

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {Γ : EffectCtx (Ty α) ε} {A : Ty α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "D[" V "]" => Ty.denote (Lifted V)

set_option backward.isDefEq.respectTransparency false in
public theorem denote_specialize (V : α → Type u) (P : PureMaps (Φ := Φ) (ε := ε) V)
    {n : Nat} {sorts : Fin n → α} {R : Ty α} (shape : ReplyShape sorts R)
    {t : Tm Empty Φ (Γ.length + 1)} (d : Derivation Φ Γ₀ (Γ.toBoundCtx.snoc R) t A)
    (ρ : BoundEnv D[V] Γ.toBoundCtx) (ξ : BoundEnv D[V] (fieldCtx sorts Γ).toBoundCtx)
    (vars : (i : Fin n) → V (sorts i))
    (fields : ∀ i, HEq (ξ (fieldIndex sorts Γ i)) (ULift.up.{u+1} (vars i)))
    (ambient : ∀ i, HEq (ξ (ambientIndex sorts Γ i)) (ρ i)) :
    (d.bsubst (shape.specializeDerivSubst Γ)).denote D[V] (instructions V P) (fun z => z.elim) ξ =
      d.denote D[V] (instructions V P) (fun z => z.elim)
        (ρ.snoc ((toSmall V R).symm (shape.denote V vars))) := by
  apply Derivation.denote_bsubst
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [lift_denote]
    exact shape.denote_derivation (fieldIndex sorts Γ) (Lifted V) (instructions V P)
      get_fieldType ξ (fun i => ⟨vars i⟩) fields
  · have eval {B : Ty α} (i : Fin (fieldCtx sorts Γ).length)
        (h : (fieldCtx sorts Γ).toBoundCtx.get i = B) :
        (h ▸ Derivation.bv (ι := i) : Derivation Φ Γ₀ (fieldCtx sorts Γ).toBoundCtx (.bv i) B).denote
          D[V] (instructions V P) (fun z => z.elim) ξ =
          pure (cast (congrArg D[V] h) (ξ i)) := by
      subst B
      rfl
    change (get_ambientType j ▸ Derivation.bv (ι := ambientIndex sorts Γ j) :
        Derivation Φ Γ₀ (fieldCtx sorts Γ).toBoundCtx _ (Γ.toBoundCtx.get j)).denote
          D[V] (instructions V P) (fun z => z.elim) ξ = pure (ρ j)
    rw [eval]
    exact congrArg pure (eq_of_heq ((cast_heq _ _).trans (ambient j)))

set_option backward.isDefEq.respectTransparency false in
public theorem specialize_of_letOp_denote_eq (V : α → Type u) (P : PureMaps (Φ := Φ) (ε := ε) V)
    {f : Φ} (hf : ¬ IsPure (⊥ : ε) f)
    {u : Tm Empty Φ Γ.length} {k l : Tm Empty Φ (Γ.length + 1)}
    (arg : Derivation Φ Γ₀ Γ.toBoundCtx u (instrSrc f))
    (dk : Derivation Φ Γ₀ (Γ.toBoundCtx.snoc (instrTrg f)) k A)
    (dl : Derivation Φ Γ₀ (Γ.toBoundCtx.snoc (instrTrg f)) l A)
    (ρ : BoundEnv D[V] Γ.toBoundCtx) {x : D[V] (instrSrc f)}
    (hx : arg.denote D[V] (instructions V P) (fun z => z.elim) ρ = pure x)
    (h : (Derivation.let₁ (.op (f := f) arg) dk).denote D[V] (instructions V P) (fun z => z.elim) ρ =
      (Derivation.let₁ (.op (f := f) arg) dl).denote D[V] (instructions V P) (fun z => z.elim) ρ)
    {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts (instrTrg f))
    (vars : (i : Fin n) → V (sorts i)) (ξ : BoundEnv D[V] (fieldCtx sorts Γ).toBoundCtx)
    (fields : ∀ i, HEq (ξ (fieldIndex sorts Γ i)) (ULift.up.{u+1} (vars i)))
    (ambient : ∀ i, HEq (ξ (ambientIndex sorts Γ i)) (ρ i)) :
    (dk.bsubst (shape.specializeDerivSubst Γ)).denote D[V] (instructions V P) (fun z => z.elim) ξ =
      (dl.bsubst (shape.specializeDerivSubst Γ)).denote D[V] (instructions V P) (fun z => z.elim) ξ := by
  simp only [Derivation.denote, hx, pure_bind] at h
  have hreply := ((eval_bind_eq_iff_shapes V P hf).mp h).2 shape vars
  rw [denote_specialize V P shape dk ρ ξ vars fields ambient,
    denote_specialize V P shape dl ρ ξ vars fields ambient]
  exact hreply

public theorem specialize_of_letOp_abortEquiv [DecidableEq α]
    (V : α → Type u) (P : PureMaps (Φ := Φ) (ε := ε) V)
    {f : Φ} (hf : ¬ IsPure (⊥ : ε) f)
    {u : Tm Empty Φ Γ.length} {k l : Tm Empty Φ (Γ.length + 1)}
    (arg : Derivation Φ Γ₀ Γ.toBoundCtx u (instrSrc f))
    (dk : Derivation Φ Γ₀ (Γ.toBoundCtx.snoc (instrTrg f)) k A)
    (dl : Derivation Φ Γ₀ (Γ.toBoundCtx.snoc (instrTrg f)) l A)
    (ρ : BoundEnv D[V] Γ.toBoundCtx) {x : D[V] (instrSrc f)}
    (hx : arg.denote D[V] (instructions V P) (fun z => z.elim) ρ = pure x)
    (h : AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (.let₁ (.op f u) k) (.let₁ (.op f u) l) A)
    {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts (instrTrg f))
    (vars : (i : Fin n) → V (sorts i)) (ξ : BoundEnv D[V] (fieldCtx sorts Γ).toBoundCtx)
    (fields : ∀ i, HEq (ξ (fieldIndex sorts Γ i)) (ULift.up.{u+1} (vars i)))
    (ambient : ∀ i, HEq (ξ (ambientIndex sorts Γ i)) (ρ i)) :
    (dk.bsubst (shape.specializeDerivSubst Γ)).denote D[V] (instructions V P) (fun z => z.elim) ξ =
      (dl.bsubst (shape.specializeDerivSubst Γ)).denote D[V] (instructions V P) (fun z => z.elim) ξ :=
  specialize_of_letOp_denote_eq V P hf arg dk dl ρ hx
    (Structured.sound V P h (.let₁ (.op arg) dk) (.let₁ (.op arg) dl) ρ)
    shape vars ξ fields ambient

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape.Proofs
