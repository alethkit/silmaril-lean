module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

/-! # Original-bound reflection of finite mixed request trees -/

public section

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv Derivation)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

open SumCall (SumSignature endpoints effects)

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {c : α}

theorem tuple_lowers {k n : Nat} (a : Fin k → Expr (Φ ⊕ Ψ)) (t : Fin k → Tm Empty (Φ ⊕ Ψ) n)
    (h : ∀ i, (a i).toLetIter n = some (t i)) :
    (sourceTuple k a).toLetIter n = some (nativeTuple k t) :=
  Proofs.tuple_lowers a t h

theorem tree_lowers {n : Nat} {ss : Fin n → α} {a : α} (p : Tree S ss a) :
    (SumCall.treeSource (Ψ := Ψ) S p).toLetIter n = some (SumCall.treeNative (Ψ := Ψ) S p) :=
  Proofs.tree_lowers S p

theorem lowers {n : Nat} {slots : Fin n → α} (p : Program S T c slots) :
    p.source.toLetIter n = some p.native :=
  Proofs.lowers S T p

/-- At the canonical valuation recover the entire dependent request. Testing
the atomic reply or both sum injections at arbitrary sorted valuations then
determines the continuation trees. -/
theorem eq_of_denote_eq {n : Nat} {slots : Fin n → α} {p q : Program S T c slots}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (slots i)),
      Program.denote S T modelSlots p vars = Program.denote S T modelSlots q vars) :
    p = q :=
  Proofs.eq_of_denote_eq S T h

section Typed

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

theorem slots_extended {a : α} (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    ∀ i : Fin (Γ.length + 1),
      (((Ty.base a, (⊥ : ε)) :: Γ).get i).1 = .base (extendSorts a slots i) :=
  Proofs.slots_extended hslots

theorem pure_extended (hΓ : Γ.Pure) (a : α) :
    EffectCtx.Pure ((Ty.base a, (⊥ : ε)) :: Γ) :=
  Proofs.pure_extended hΓ a

theorem tree_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    {a : α} (p : Tree S slots a) (hp : DeclaredPure (ε := ε) S p) (e : ε) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ (SumCall.treeSource (Ψ := Ψ) S p) (.base a) e :=
  Proofs.tree_wf S T hΓ hslots p hp e

theorem atom_request_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    {f : Φ} (args : Args S slots f) (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    {e : ε} (hf : instrEff f ≤ e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ (.op (Sum.inl f : Φ ⊕ Ψ) (sourceTuple (S.arity f) (fun i => SumCall.treeSource S (args i))))
      (Ty.base (S.out f)) e :=
  Proofs.atom_request_wf S T hΓ hslots args hargs hf

theorem sum_request_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    {f : Ψ} (args : SumCall.SumArgs S T slots f) (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    {e : ε} (hf : instrEff f ≤ e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ (.op (Sum.inr f) (sourceTuple (T.arity f) (fun i => SumCall.treeSource S (args i))))
      (SumCall.result T f) e :=
  Proofs.sum_request_wf S T hΓ hslots args hargs hf

theorem source_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T c slots) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ p.source (.base c) e :=
  Proofs.source_wf S T hΓ hslots e p hp

section Requests

variable {m : Nat} (modelSlots : Fin m → α)

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "D" => Ty.denote (Atom S modelSlots)
local notation "M" => SumCall.instructions (ε := ε) S T modelSlots

omit [HasEff Ψ ε] in
/-- A pure atomic tree evaluates to its free-algebra value at any sorted valuation. -/
theorem eval_tree_exists (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    {a : α} (p : Tree S slots a) (hp : DeclaredPure (ε := ε) S p) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ Γ.toBoundCtx (SumCall.treeNative S p) (.base a),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote D M (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
          ITree.ret ⟨p.interpret S (Tree S modelSlots) Tree.op vars⟩ :=
  Proofs.eval_tree_exists S T modelSlots hslots p hp

omit [HasEff Ψ ε] in
/-- Evaluate the entire tuple of pure operands before issuing a request. -/
theorem eval_args_exists (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    {k : Nat} {as : Fin k → α} (args : (i : Fin k) → Tree S slots (as i))
    (hp : ∀ i, DeclaredPure (ε := ε) S (args i)) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ Γ.toBoundCtx (nativeTuple k (fun i => SumCall.treeNative S (args i))) (input k as),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote D M (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
          ITree.ret (packArgs S modelSlots k as (fun i => (args i).interpret S _ Tree.op vars)) :=
  Proofs.eval_args_exists S T modelSlots hslots args hp

omit [HasEff Ψ ε] in
theorem eval_atom_visible (f : Φ) (args : Args S modelSlots f) (hf : ¬ IsPure (⊥ : ε) f) :
    letI := endpoints S T
    (M).eval (.inl f) (packArgs S modelSlots (S.arity f) (S.arg f) args) =
      ITree.vis (.atom f args) (fun r => ITree.ret ⟨r⟩) :=
  Proofs.eval_atom_visible S T modelSlots f args hf

omit [HasEff Ψ ε] in
theorem eval_sum_request (g : Ψ) (args : SumCall.SumArgs S T modelSlots g) :
    letI := endpoints S T
    (M).eval (.inr g) (packArgs S modelSlots (T.arity g) (T.arg g) args) =
      ITree.vis (.sum g args) (fun r => ITree.ret (SumCall.responseValue S T modelSlots r)) :=
  Proofs.eval_sum_request S T modelSlots g args

end Requests

/-- Native evaluation follows the request tree at every sorted valuation,
binding each actual reply before evaluating the corresponding child. -/
theorem eval_exists {m : Nat} (modelSlots : Fin m → α)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Program S T c slots) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native (.base c),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote (Ty.denote (Atom S modelSlots)) (SumCall.instructions (ε := ε) S T modelSlots)
          (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
            Program.denote S T modelSlots p vars :=
  Proofs.eval_exists S T modelSlots hslots e p hp

/-- Visible sum instructions respect the purity premise of native soundness
when every sum primitive is declared non-bottom. -/
theorem instructions_respectsPure {m : Nat} (modelSlots : Fin m → α)
    (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    InstructionModel.RespectsPure (ε := ε) (SumCall.instructions (ε := ε) S T modelSlots) :=
  Proofs.instructions_respectsPure S T modelSlots visible

variable [DecidableEq α]

/-- Native equality recovers the primitive, every input and all normalized
continuations, recursively. All additional sum instructions are declared non-bottom so
the model is sound for native proofs with arbitrary typed intermediates. -/
theorem native_eq_implies_eq (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T c slots) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q)
    (hn : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native (.base c)) :
    p = q :=
  Proofs.native_eq_implies_eq S T visible hslots e p q hp hq hn

variable [EffectIteration ε]

/-- Reflection at the supplied source bound for independently specified
normalized finite request trees of atomic result. -/
theorem endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T c slots) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native (.base c) ↔
      Eqv Γ (.base c) e p.source q.source :=
  Proofs.endpoint_reflection S T visible hΓ hslots e p q hp hq

end Typed

section Embeddings

variable {n : Nat} {ss : Fin n → α}

/-- Rendering an embedded atomic sequence agrees with its atomic-arm lowering. -/
theorem ofSequence_source (p : Sequence S c ss) :
    (ofSequence S T p).source = SumCall.armSource S p :=
  Proofs.ofSequence_source S T p

theorem ofSequence_native (p : Sequence S c ss) :
    (ofSequence S T p).native = SumCall.armNative S p :=
  Proofs.ofSequence_native S T p

theorem ofSequence_denote {m : Nat} (ms : Fin m → α) (p : Sequence S c ss)
    (vars : (i : Fin n) → Tree S ms (ss i)) :
    Program.denote S T ms (ofSequence S T p) vars =
      Sequence.denoteWith S ms SumCall.Event.atom p vars :=
  Proofs.ofSequence_denote S T ms p vars

theorem ofSequence_injective : Function.Injective (ofSequence S T (c := c) (slots := ss)) :=
  Proofs.ofSequence_injective S T

/-- Embedding the earlier single-sum-call fragment preserves both renderings. -/
theorem ofSumCall_source (p : SumCall.Program S T ss c) :
    (ofSumCall S T p).source = p.source :=
  Proofs.ofSumCall_source S T p

theorem ofSumCall_native (p : SumCall.Program S T ss c) :
    (ofSumCall S T p).native = p.native :=
  Proofs.ofSumCall_native S T p

theorem ofSumCall_denote {m : Nat} (ms : Fin m → α) (p : SumCall.Program S T ss c)
    (vars : (i : Fin n) → Tree S ms (ss i)) :
    Program.denote S T ms (ofSumCall S T p) vars = SumCall.Program.denote S T ms p vars :=
  Proofs.ofSumCall_denote S T ms p vars

theorem ofSumCall_injective : Function.Injective (ofSumCall S T (c := c) (slots := ss)) :=
  Proofs.ofSumCall_injective S T

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]

theorem ofSequence_wellTyped (e : ε) (p : Sequence S c ss) :
    Program.WellTyped S T e (ofSequence S T p) ↔ Sequence.WellTyped S e p :=
  Proofs.ofSequence_wellTyped S T e p

theorem ofSumCall_wellTyped (e : ε) (p : SumCall.Program S T ss c) :
    Program.WellTyped S T e (ofSumCall S T p) ↔ SumCall.Program.WellTyped S T e p :=
  Proofs.ofSumCall_wellTyped S T e p

end Embeddings

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed
