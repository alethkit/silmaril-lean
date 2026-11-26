module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured

/-! # Request observations and native soundness for structured responses -/

public section

open Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured

universe u v r

variable {α Φ : Type u} [HasTy Φ (Ty α)] (V : α → Type u)

/-- A visible node exposes its request even if its response type is empty. -/
theorem head_of_vis {B : Type v} (f : Φ) (x : Ty.denote V (instrSrc f))
    (k : Ty.denote V (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B) :
    headRequest V (ITree.vis (.call f x) k) = Part.some (some ⟨f, x⟩) :=
  Proofs.head_of_vis V f x k

/-- Equality of two visible nodes recovers their full dependent request. -/
theorem request_eq_of_vis_eq {B : Type v} {f g : Φ}
    {x : Ty.denote V (instrSrc f)} {y : Ty.denote V (instrSrc g)}
    {k : Ty.denote V (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B}
    {l : Ty.denote V (instrTrg g) → ITree.Tree (Event (Φ := Φ) V) B}
    (h : ITree.vis (.call f x) k = ITree.vis (.call g y) l) :
    (⟨f, x⟩ : Request (Φ := Φ) V) = ⟨g, y⟩ :=
  Proofs.request_eq_of_vis_eq V h

/-- Two calls to the same primitive agree exactly when their arguments
and all their typed reply continuations agree. -/
theorem vis_eq_iff {B : Type v} {f : Φ} {x y : Ty.denote V (instrSrc f)}
    {k l : Ty.denote V (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B} :
    ITree.vis (.call f x) k = ITree.vis (.call f y) l ↔ x = y ∧ ∀ reply, k reply = l reply :=
  Proofs.vis_eq_iff V

section MapExistence

variable {ε : Type r} [HasEff Φ ε] [Bot ε] (F : α → Type v)

/-- Inhabitedness preservation by every bottom-pure primitive exactly
characterizes existence of a total map family on the chosen carriers. -/
theorem nonempty_pureMaps_iff :
    Nonempty (PureMaps (Φ := Φ) (ε := ε) F) ↔
      ∀ f : Φ, IsPure (⊥ : ε) f →
        Nonempty (Ty.denote F (instrSrc f)) → Nonempty (Ty.denote F (instrTrg f)) :=
  Proofs.nonempty_pureMaps_iff F

/-- A bottom-pure unit-to-empty instruction precludes this set-valued
model on every atomic interpretation. -/
theorem no_pureMaps_of_unit_to_empty {f : Φ}
    (hf : IsPure (⊥ : ε) f) (input : instrSrc f = (Ty.unit : Ty α))
    (output : instrTrg f = (Ty.empty : Ty α)) :
    ¬ Nonempty (PureMaps (Φ := Φ) (ε := ε) F) :=
  Proofs.no_pureMaps_of_unit_to_empty F hf input output

/-- The obstruction applies to every set-valued monadic instruction model
with the same purity condition, independently of the chosen monad. -/
theorem not_respectsPure_of_unit_to_empty (F : α → Type v)
    {m : Type v → Type v} [Pure m] (M : InstructionModel (Ty.denote F) Φ m) {f : Φ}
    (hf : IsPure (⊥ : ε) f) (input : instrSrc f = (Ty.unit : Ty α))
    (output : instrTrg f = (Ty.empty : Ty α)) :
    ¬ InstructionModel.RespectsPure (ε := ε) M :=
  Proofs.not_respectsPure_of_unit_to_empty F M hf input output

end MapExistence

variable {ε : Type r} [HasEff Φ ε] [Bot ε] (P : PureMaps (Φ := Φ) (ε := ε) V)

/-- The supplied pure maps witness the purity premise of native soundness. -/
theorem respectsPure : InstructionModel.RespectsPure (ε := ε) (instructions V P) :=
  Proofs.respectsPure V P

/-- A nonpure instruction exposes its request before entering the
continuation, including when there are no possible replies. -/
theorem eval_bind_of_not_pure {B : Type (u + 1)} {f : Φ} (hf : ¬ IsPure (⊥ : ε) f)
    (x : Ty.denote (Lifted V) (instrSrc f))
    (k : Ty.denote (Lifted V) (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B) :
    ((instructions V P).eval f x >>= k) =
      ITree.vis (.call f (toSmall V (instrSrc f) x)) (fun reply => k ((toSmall V (instrTrg f)).symm reply)) :=
  Proofs.eval_bind_of_not_pure V P hf x k

/-- A comparison of two calls to the same nonpure primitive tests the full
input and every typed reply, with arbitrary effectful continuations. -/
theorem eval_bind_eq_iff {B : Type (u + 1)} {f : Φ} (hf : ¬ IsPure (⊥ : ε) f)
    {x y : Ty.denote (Lifted V) (instrSrc f)}
    {k l : Ty.denote (Lifted V) (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B} :
    ((instructions V P).eval f x >>= k) = ((instructions V P).eval f y >>= l) ↔
      x = y ∧ ∀ reply : Ty.denote V (instrTrg f),
        k ((toSmall V (instrTrg f)).symm reply) = l ((toSmall V (instrTrg f)).symm reply) :=
  Proofs.eval_bind_eq_iff V P hf

/-- Native evaluation first evaluates the argument, then emits one request,
and only then evaluates the continuation in the response environment. -/
theorem denote_letOp_of_not_pure {n : Nat} {β : BoundCtx (Ty α) n}
    {f : Φ} (hf : ¬ IsPure (⊥ : ε) f) {a : Tm Empty Φ n} {k : Tm Empty Φ (n + 1)} {B : Ty α}
    (arg : Derivation Φ .nil β a (instrSrc f))
    (next : Derivation Φ .nil (β.snoc (instrTrg f)) k B)
    (ρ : BoundEnv (Ty.denote (Lifted V)) β) :
    (Derivation.let₁ (.op (f := f) arg) next).denote (Ty.denote (Lifted V)) (instructions V P) (fun x => x.elim) ρ =
      (arg.denote (Ty.denote (Lifted V)) (instructions V P) (fun x => x.elim) ρ >>= fun x =>
        ITree.vis (.call f (toSmall V (instrSrc f) x)) (fun reply =>
          next.denote (Ty.denote (Lifted V)) (instructions V P) (fun x => x.elim)
            (ρ.snoc ((toSmall V (instrTrg f)).symm reply)))) :=
  Proofs.denote_letOp_of_not_pure V P hf arg next ρ

/-- Native abort equivalence preserves all observations in this model for
any supplied total pure maps and any bound environment. -/
theorem sound [DecidableEq α] {n : Nat} {β : BoundCtx (Ty α) n}
    {a b : Tm Empty Φ n} {A : Ty α}
    (h : AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) β a b A)
    (da : Derivation Φ .nil β a A) (db : Derivation Φ .nil β b A)
    (ρ : BoundEnv (Ty.denote (Lifted V)) β) :
    da.denote (Ty.denote (Lifted V)) (instructions V P) (fun x => x.elim) ρ =
      db.denote (Ty.denote (Lifted V)) (instructions V P) (fun x => x.elim) ρ :=
  Proofs.sound V P h da db ρ

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured
