module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply

/-! # Reifying replies and comparing the continuations of structured calls -/

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation AbortEquiv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured

universe u v w r

variable {α : Type u}

namespace ReplyShape

/-- Every semantic reply is a constructor expression applied to sorted
values. A sum introduces slots only in the branch that actually responds. -/
theorem exists_shape (V : α → Type v) {A : Ty α} (reply : Ty.denote V A) :
    ∃ (n : Nat) (ss : Fin n → α) (shape : ReplyShape ss A) (vars : (i : Fin n) → V (ss i)),
      shape.denote V vars = reply :=
  Proofs.exists_shape V reply

variable {n m : Nat} {ss : Fin n → α} {A : Ty α} (s : ReplyShape ss A) (place : Fin n → Fin m)

/-- The two syntax renderings agree under the usual source lowering. -/
theorem lowers {Φ : Type w} : (s.source (Φ := Φ) place).toLetIter m = some (s.native place) :=
  Proofs.lowers s place

/-- Placing the atoms in pure source slots gives a bottom-typed reply. -/
theorem wf {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Preorder ε] [OrderBot ε]
    {Γ : EffectCtx (Ty α) ε} (place : Fin n → Fin Γ.length)
    (hs : ∀ i, Γ.get (place i) = (.base (ss i), (⊥ : ε))) :
    Wf Γ (s.source place : Expr Φ) A (⊥ : ε) :=
  Proofs.wf s place hs

/-- A rendered reply under a matching valuation immediately returns its
constructor interpretation. The instruction model is arbitrary. -/
theorem denote_derivation {Φ : Type w} [HasTy Φ (Ty α)] (V : α → Type v)
    {M : Type v → Type v} [Monad M] [LawfulMonad M] [Iterate M]
    (instr : InstructionModel (Ty.denote V) Φ M) {β : BoundCtx (Ty α) m}
    (ht : ∀ i, β.get (place i) = .base (ss i))
    (ρ : BoundEnv (Ty.denote V) β) (vars : (i : Fin n) → V (ss i))
    (hρ : ∀ i, HEq (ρ (place i)) (vars i)) :
    (s.derivation (Φ := Φ) place ht).denote (Ty.denote V) instr (fun x => x.elim) ρ =
      pure (s.denote V vars) :=
  Proofs.denote_derivation s place V instr ht ρ vars hρ

/-- The event-to-monad lift of a reified reply is the same constructor
value with precisely its atomic fields lifted. -/
theorem lift_denote (V : α → Type u) (vars : (i : Fin n) → V (ss i)) :
    (toSmall V A).symm (s.denote V vars) =
      s.denote (Lifted V) (fun i => ⟨vars i⟩) :=
  Proofs.lift_denote s V vars

end ReplyShape

/-- Test continuation equality on the constructor shapes of the reply with
arbitrary sorted valuations. For an empty reply there are no tests, and the
visible request and its argument are still compared. -/
theorem eval_bind_eq_iff_shapes {Φ : Type u} [HasTy Φ (Ty α)] (V : α → Type u)
    {ε : Type r} [HasEff Φ ε] [Bot ε] (P : PureMaps (Φ := Φ) (ε := ε) V)
    {B : Type (u + 1)} {f : Φ} (hf : ¬ IsPure (⊥ : ε) f)
    {x y : Ty.denote (Lifted V) (instrSrc f)}
    {k l : Ty.denote (Lifted V) (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B} :
    ((instructions V P).eval f x >>= k) = ((instructions V P).eval f y >>= l) ↔
      x = y ∧ ∀ {n : Nat} {ss : Fin n → α} (s : ReplyShape ss (instrTrg f)) (vars : (i : Fin n) → V (ss i)),
        k ((toSmall V (instrTrg f)).symm (s.denote V vars)) =
          l ((toSmall V (instrTrg f)).symm (s.denote V vars)) :=
  ReplyShape.Proofs.eval_bind_eq_iff_shapes V P hf

/-- Native equality between calls to the same nonpure instruction entails
agreement of the returned arguments and of the continuations at every
reified reply. The premises describe the argument denotations at this
valuation. The continuations may use the entire native syntax. -/
theorem letOp_observations_of_abortEquiv {Φ : Type u} [HasTy Φ (Ty α)] [DecidableEq α] (V : α → Type u)
    {ε : Type r} [HasEff Φ ε] [Bot ε] (P : PureMaps (Φ := Φ) (ε := ε) V)
    {n : Nat} {β : BoundCtx (Ty α) n} {f : Φ} (hf : ¬ IsPure (⊥ : ε) f)
    {a b : Tm Empty Φ n} {k l : Tm Empty Φ (n + 1)} {B : Ty α}
    (da : Derivation Φ .nil β a (instrSrc f)) (db : Derivation Φ .nil β b (instrSrc f))
    (dk : Derivation Φ .nil (β.snoc (instrTrg f)) k B) (dl : Derivation Φ .nil (β.snoc (instrTrg f)) l B)
    (ρ : BoundEnv (Ty.denote (Lifted V)) β)
    {x y : Ty.denote (Lifted V) (instrSrc f)}
    (ha : da.denote (Ty.denote (Lifted V)) (instructions V P) (fun z => z.elim) ρ = pure x)
    (hb : db.denote (Ty.denote (Lifted V)) (instructions V P) (fun z => z.elim) ρ = pure y)
    (h : AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) β (.let₁ (.op f a) k) (.let₁ (.op f b) l) B) :
    x = y ∧ ∀ {m : Nat} {ss : Fin m → α} (shape : ReplyShape ss (instrTrg f)) (vars : (i : Fin m) → V (ss i)),
      let reply := (toSmall V (instrTrg f)).symm (shape.denote V vars)
      dk.denote (Ty.denote (Lifted V)) (instructions V P) (fun z => z.elim) (ρ.snoc reply) =
        dl.denote (Ty.denote (Lifted V)) (instructions V P) (fun z => z.elim) (ρ.snoc reply) :=
  ReplyShape.Proofs.letOp_observations_of_abortEquiv V P hf da db dk dl ρ ha hb h

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured
