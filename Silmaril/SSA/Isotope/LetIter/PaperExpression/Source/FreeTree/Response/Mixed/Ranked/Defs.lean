module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Defs

/-! # Finite ranked expansions of native loops -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv HasTypeEffect)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature SumArgs)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked

universe u r

variable {α Φ Ψ ι : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) (rank : ι → Nat)
  {c : α}

/-- A finite one-step tree. Each repeat carries a control state of strictly
smaller rank. Request replies can choose different repeat states. -/
inductive Step (c : α) (k : Nat) : {n : Nat} → (Fin n → α) → Type (u + 1)
  | done {n : Nat} {ss : Fin n → α} : Raw.Program S T c ss → Step c k ss
  | again {n : Nat} {ss : Fin n → α} (i : ι) : rank i < k → Step c k ss
  | atom {n : Nat} {ss : Fin n → α} (f : Φ) :
      Args S ss f → Step c k (extendSorts (S.out f) ss) → Step c k ss
  | sum {n : Nat} {ss : Fin n → α} (g : Ψ) :
      SumArgs S T ss g → Step c k (extendSorts (T.left g) ss) →
        Step c k (extendSorts (T.right g) ss) → Step c k ss

namespace Step

variable {k : Nat}
variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε]

def WellTyped (e : ε) : {n : Nat} → {ss : Fin n → α} → Step S T rank c k ss → Prop
  | _, _, .done p => Raw.Program.WellTyped S T e p
  | _, _, .again _ _ => True
  | _, _, .atom f args next =>
      (∀ i, DeclaredPure (ε := ε) S (args i)) ∧ ¬ IsPure (⊥ : ε) f ∧
        instrEff f ≤ e ∧ WellTyped e next
  | _, _, .sum g args left right =>
      (∀ i, DeclaredPure (ε := ε) S (args i)) ∧ instrEff g ≤ e ∧
        WellTyped e left ∧ WellTyped e right

/-- Render one step, plugging actual native continuations at the repeat sites. -/
noncomputable def native (resume : ∀ {n : Nat}, (Fin n → α) → ι → Tm Empty (Φ ⊕ Ψ) n) :
    {n : Nat} → {ss : Fin n → α} → Step S T rank c k ss → Tm Empty (Φ ⊕ Ψ) n
  | _, _, .done p => (Raw.Program.compile (ε := ε) S T p).native
  | _, ss, .again i _ => resume ss i
  | _, _, .atom f args next =>
      .let₁ (.op (.inl f) (nativeTuple (S.arity f) (fun i => SumCall.treeNative S (args i)))) (native resume next)
  | _, _, .sum g args left right =>
      .case (.op (.inr g) (nativeTuple (T.arity g) (fun i => SumCall.treeNative S (args i))))
        (native resume left) (native resume right)

/-- Plug expanded mixed trees at the strictly smaller repeat sites. -/
noncomputable def expand (resume : ∀ {n : Nat} (ss : Fin n → α) (i : ι),
    rank i < k → Mixed.Program S T c ss) :
    {n : Nat} → {ss : Fin n → α} → Step S T rank c k ss → Mixed.Program S T c ss
  | _, _, .done p => Raw.Program.compile (ε := ε) S T p
  | _, ss, .again i hi => resume ss i hi
  | _, _, .atom f args next => .atom f args (expand resume next)
  | _, _, .sum g args left right => .sum g args (expand resume left) (expand resume right)

end Step

/-- A one-step presentation of a family of native endpoints at every atomic
scope. Its local unfolding equations are checked separately. -/
structure System (c : α) where
  endpoint : ∀ {n : Nat}, (Fin n → α) → ι → Tm Empty (Φ ⊕ Ψ) n
  step : ∀ {n : Nat} (ss : Fin n → α) (i : ι), Step S T rank c (rank i) ss

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- Compute a finite tree by well-founded recursion on the control rank. -/
noncomputable def System.expand (sys : System S T rank c) (i : ι)
    {n : Nat} (ss : Fin n → α) : Mixed.Program S T c ss :=
  Step.expand (ε := ε) S T rank (fun ss j _ => sys.expand j ss) (sys.step ss i)
termination_by rank i

variable [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

/-- The certificate checks native typing at the original bound and compares
each endpoint with just its one-step tree, where repeats are still native
endpoints. It contains no expanded tree. -/
structure System.Checked (sys : System S T rank c) (e : ε) : Prop where
  step_typed : ∀ {n : Nat} (ss : Fin n → α) (i : ι), Step.WellTyped S T rank e (sys.step ss i)
  endpoint_typed : ∀ {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α},
    Γ.Pure → (∀ j, (Γ.get j).1 = .base (ss j)) → ∀ i,
    letI := SumCall.endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := SumCall.effects
    HasTypeEffect (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx (sys.endpoint ss i) (.base c) e
  unfold : ∀ {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α},
    Γ.Pure → (∀ j, (Γ.get j).1 = .base (ss j)) → ∀ i,
    letI := SumCall.endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := SumCall.effects
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx (sys.endpoint ss i)
      (Step.native (ε := ε) S T rank sys.endpoint (sys.step ss i)) (.base c)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked
