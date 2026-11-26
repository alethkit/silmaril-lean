module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Observation.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Observation

/-! # Evaluation of reply-specialized continuations -/

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation AbortEquiv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {Γ : EffectCtx (Ty α) ε} {A : Ty α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "D[" V "]" => Ty.denote (Lifted V)

/-- Native substitution evaluates the original body at the shaped reply
and the retained ambient valuation. -/
theorem denote_specialize (V : α → Type u) (P : PureMaps (Φ := Φ) (ε := ε) V)
    {n : Nat} {sorts : Fin n → α} {R : Ty α} (shape : ReplyShape sorts R)
    {t : Tm Empty Φ (Γ.length + 1)} (d : Derivation Φ Γ₀ (Γ.toBoundCtx.snoc R) t A)
    (ρ : BoundEnv D[V] Γ.toBoundCtx) (ξ : BoundEnv D[V] (fieldCtx sorts Γ).toBoundCtx)
    (vars : (i : Fin n) → V (sorts i))
    (fields : ∀ i, HEq (ξ (fieldIndex sorts Γ i)) (ULift.up.{u+1} (vars i)))
    (ambient : ∀ i, HEq (ξ (ambientIndex sorts Γ i)) (ρ i)) :
    (d.bsubst (shape.specializeDerivSubst Γ)).denote D[V] (instructions V P) (fun z => z.elim) ξ =
      d.denote D[V] (instructions V P) (fun z => z.elim)
        (ρ.snoc ((toSmall V R).symm (shape.denote V vars))) :=
  Proofs.denote_specialize V P shape d ρ ξ vars fields ambient

/-- Equal observations of one shared nonpure request, whose argument
returns a value, agree after every matching reply substitution. -/
theorem specialize_of_letOp_denote_eq (V : α → Type u) (P : PureMaps (Φ := Φ) (ε := ε) V)
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
      (dl.bsubst (shape.specializeDerivSubst Γ)).denote D[V] (instructions V P) (fun z => z.elim) ξ :=
  Proofs.specialize_of_letOp_denote_eq V P hf arg dk dl ρ hx h shape vars ξ fields ambient

/-- Native equality of a shared visible request gives equality of
observations of its substituted continuations. The argument must return
a value at the retained valuation. -/
theorem specialize_of_letOp_abortEquiv [DecidableEq α]
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
  Proofs.specialize_of_letOp_abortEquiv V P hf arg dk dl ρ hx h shape vars ξ fields ambient

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape
