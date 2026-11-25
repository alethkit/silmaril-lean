module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall

/-! # Original-bound reflection for one response-bearing source call -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv Derivation)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.Semantics Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall

universe u r

section Evaluation

variable {α Φ : Type u} (S : Signature α Φ) {n : Nat} (modelSlots : Fin n → α)
  {ε : Type r} [HasEff Φ ε] [Bot ε] {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "β" => Γ.toBoundCtx
local notation "D" => Ty.denote (Atom S modelSlots)
local notation "M" => instructions (ε := ε) S modelSlots

/-- Evaluate a pure normal tree under any sorted valuation in the response model. -/
theorem eval_tree_exists {c : α} (p : Tree S slots c) (hp : DeclaredPure (ε := ε) S p)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    letI := S.endpoints
    ∃ d : Derivation Φ Γ₀ β p.native (.base c),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote D M (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
          ITree.ret ⟨p.interpret S (Tree S modelSlots) Tree.op vars⟩ :=
  Proofs.eval_tree_exists S modelSlots p hp hslots

/-- Evaluate a normalized request under any sorted valuation in the response model. -/
theorem eval_request_exists {f : Φ} (args : Args S slots f)
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i)) (hf : ¬ IsPure (⊥ : ε) f)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    letI := S.endpoints
    ∃ d : Derivation Φ Γ₀ β (Tree.op f args).native (.base (S.out f)),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote D M (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
          ITree.vis (.call f (fun i => (args i).interpret S (Tree S modelSlots) Tree.op vars))
            (fun r => ITree.ret ⟨r⟩) :=
  Proofs.eval_request_exists S modelSlots args hargs hf hslots

end Evaluation

variable {α Φ : Type u} (S : Signature α Φ) {ε : Type r} [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] [DecidableEq α]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α} {f : Φ} {c : α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "Γ⁺" => ((Ty.base (S.out f), (⊥ : ε)) :: Γ)
local notation "β" => Γ.toBoundCtx

/-- A native equality between calls with the same normalized request reflects
to source equality of their pure atomic continuations at the supplied bound.
The continuations are typed in the context extended by the response sort. -/
theorem continuation_eqv
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (args : (i : Fin (S.arity f)) → Tree S slots (S.arg f i))
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hf : ¬ IsPure (⊥ : ε) f) (e : ε) (he : instrEff f ≤ e)
    {a b : Expr Φ}
    (ha : letI := S.endpoints; Wf Γ⁺ a (.base c) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ⁺ b (.base c) (⊥ : ε))
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : a.toLetIter (Γ.length + 1) = some t) (hs : b.toLetIter (Γ.length + 1) = some s)
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (Tree.op f args).native t)
        (.let₁ (Tree.op f args).native s) (.base c)) :
    letI := S.endpoints
    Eqv Γ⁺ (.base c) e a b :=
  Proofs.continuation_eqv S hΓ hslots args hargs hf e he ha hb ht hs hn

/-- Original-bound reflection for a single non-bottom call with a shared
pure normalized argument tuple and bottom-typed continuations of atomic
result. The native equality may have arbitrary well-typed intermediates. -/
theorem endpoint_reflection
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (args : (i : Fin (S.arity f)) → Tree S slots (S.arg f i))
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hf : ¬ IsPure (⊥ : ε) f) (e : ε) (he : instrEff f ≤ e)
    {a b : Expr Φ}
    (ha : letI := S.endpoints; Wf Γ⁺ a (.base c) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ⁺ b (.base c) (⊥ : ε))
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : a.toLetIter (Γ.length + 1) = some t) (hs : b.toLetIter (Γ.length + 1) = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (Tree.op f args).native t)
        (.let₁ (Tree.op f args).native s) (.base c) ↔
      Eqv Γ (.base c) e (.let₁ (Tree.op f args).source a) (.let₁ (Tree.op f args).source b) :=
  Proofs.endpoint_reflection S hΓ hslots args hargs hf e he ha hb ht hs

omit [DecidableEq α] in
/-- Interpreting a tree at the canonical variable valuation returns that tree. -/
theorem interpret_vars {n : Nat} {ss : Fin n → α} {a : α} (p : Tree S ss a) :
    p.interpret S (Tree S ss) Tree.op Tree.var = p :=
  Proofs.interpret_vars S p

omit [EffectIteration ε] [DecidableEq α] in
/-- A normalized request has its declared result sort at the supplied bound. -/
theorem request_wf (args : (i : Fin (S.arity f)) → Tree S slots (S.arg f i))
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) {e : ε}
    (he : instrEff f ≤ e) :
    letI := S.endpoints
    Wf Γ (Tree.op f args).source (.base (S.out f)) e :=
  Proofs.request_wf S args hargs hΓ hslots he

omit [EffectIteration ε] in
/-- Native equality of two visible calls identifies both the primitive and its typed arguments. -/
theorem request_eq {g : Φ}
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (args : Args S slots f) (other : Args S slots g)
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hother : ∀ i, DeclaredPure (ε := ε) S (other i))
    (hf : ¬ IsPure (⊥ : ε) f) (hg : ¬ IsPure (⊥ : ε) g)
    {t s : Tm Empty Φ (Γ.length + 1)}
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (Tree.op f args).native t)
        (.let₁ (Tree.op g other).native s) (.base c)) :
    (⟨f, args⟩ : Request S slots) = ⟨g, other⟩ :=
  Proofs.request_eq S hslots args other hargs hother hf hg hn

/-- Single-call reflection with independently specified normalized requests. -/
theorem endpoint_reflection_independent_requests {g : Φ}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (args : Args S slots f) (other : Args S slots g)
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hother : ∀ i, DeclaredPure (ε := ε) S (other i))
    (hf : ¬ IsPure (⊥ : ε) f) (hg : ¬ IsPure (⊥ : ε) g) (e : ε)
    (he : instrEff f ≤ e) (_he' : instrEff g ≤ e)
    {a b : Expr Φ}
    (ha : letI := S.endpoints; Wf Γ⁺ a (.base c) (⊥ : ε))
    (hb : letI := S.endpoints; Wf ((Ty.base (S.out g), (⊥ : ε)) :: Γ) b (.base c) (⊥ : ε))
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : a.toLetIter (Γ.length + 1) = some t) (hs : b.toLetIter (Γ.length + 1) = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (Tree.op f args).native t)
        (.let₁ (Tree.op g other).native s) (.base c) ↔
      Eqv Γ (.base c) e (.let₁ (Tree.op f args).source a) (.let₁ (Tree.op g other).source b) :=
  Proofs.endpoint_reflection_independent_requests S hΓ hslots args other hargs hother hf hg e he _he' ha hb ht hs

/-- Independently normalize both pure argument expressions before comparing the
requests. The reconstructed source equation uses primitive and let congruence
at the supplied bound. -/
theorem endpoint_reflection_pure_arguments {g : Φ}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (hf : ¬ IsPure (⊥ : ε) f) (hg : ¬ IsPure (⊥ : ε) g) (e : ε)
    (he : instrEff f ≤ e) (he' : instrEff g ≤ e)
    {x y a b : Expr Φ}
    (hx : letI := S.endpoints; Wf Γ x (input (S.arity f) (S.arg f)) (⊥ : ε))
    (hy : letI := S.endpoints; Wf Γ y (input (S.arity g) (S.arg g)) (⊥ : ε))
    (ha : letI := S.endpoints; Wf Γ⁺ a (.base c) (⊥ : ε))
    (hb : letI := S.endpoints; Wf ((Ty.base (S.out g), (⊥ : ε)) :: Γ) b (.base c) (⊥ : ε))
    {x₀ y₀ : Tm Empty Φ Γ.length} {t s : Tm Empty Φ (Γ.length + 1)}
    (hlx : x.toLetIter Γ.length = some x₀) (hly : y.toLetIter Γ.length = some y₀)
    (ht : a.toLetIter (Γ.length + 1) = some t) (hs : b.toLetIter (Γ.length + 1) = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (.op f x₀) t) (.let₁ (.op g y₀) s) (.base c) ↔
      Eqv Γ (.base c) e (.let₁ (.op f x) a) (.let₁ (.op g y) b) :=
  Proofs.endpoint_reflection_pure_arguments S hΓ hslots hf hg e he he' hx hy ha hb hlx hly ht hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall
