module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Defs

/-! # Finite ranked expansions of native loops -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv HasTypeEffect)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature SumArgs)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Scoped

universe u v r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {State : ∀ {n : Nat}, (Fin n → α) → Type v}
  (rank : ∀ {n : Nat} {ss : Fin n → α}, State ss → Nat)
  {c : α}

/-- A finite one-step tree. Each repeat carries a control state of strictly
smaller rank. Request replies can choose different repeat states. -/
inductive Step (c : α) (k : Nat) : {n : Nat} → (Fin n → α) → Type (max (u + 1) v)
  | done {n : Nat} {ss : Fin n → α} : Raw.Program S T c ss → Step c k ss
  | again {n : Nat} {ss : Fin n → α} (i : State ss) : rank i < k → Step c k ss
  | atom {n : Nat} {ss : Fin n → α} (f : Φ) :
      Args S ss f → Step c k (extendSorts (S.out f) ss) → Step c k ss
  | sum {n : Nat} {ss : Fin n → α} (g : Ψ) :
      SumArgs S T ss g → Step c k (extendSorts (T.left g) ss) →
        Step c k (extendSorts (T.right g) ss) → Step c k ss

namespace Step

variable {k : Nat}
variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε]

def WellTyped (e : ε) : {n : Nat} → {ss : Fin n → α} → Step S T (@rank) c k ss → Prop
  | _, _, .done p => Raw.Program.WellTyped S T e p
  | _, _, .again _ _ => True
  | _, _, .atom f args next =>
      (∀ i, DeclaredPure (ε := ε) S (args i)) ∧ ¬ IsPure (⊥ : ε) f ∧
        instrEff f ≤ e ∧ WellTyped e next
  | _, _, .sum g args left right =>
      (∀ i, DeclaredPure (ε := ε) S (args i)) ∧ instrEff g ≤ e ∧
        WellTyped e left ∧ WellTyped e right

/-- Render one step, plugging actual native continuations at the repeat sites. -/
noncomputable def native (resume : ∀ {n : Nat}, (ss : Fin n → α) → State ss → Tm Empty (Φ ⊕ Ψ) n) :
    {n : Nat} → {ss : Fin n → α} → Step S T (@rank) c k ss → Tm Empty (Φ ⊕ Ψ) n
  | _, _, .done p => (Raw.Program.compile (ε := ε) S T p).native
  | _, ss, .again i _ => resume ss i
  | _, _, .atom f args next =>
      .let₁ (.op (.inl f) (nativeTuple (S.arity f) (fun i => SumCall.treeNative S (args i)))) (native resume next)
  | _, _, .sum g args left right =>
      .case (.op (.inr g) (nativeTuple (T.arity g) (fun i => SumCall.treeNative S (args i))))
        (native resume left) (native resume right)

/-- Plug expanded mixed trees at the strictly smaller repeat sites. -/
noncomputable def expand (resume : ∀ {n : Nat} (ss : Fin n → α) (i : State ss),
    rank i < k → Mixed.Program S T c ss) :
    {n : Nat} → {ss : Fin n → α} → Step S T (@rank) c k ss → Mixed.Program S T c ss
  | _, _, .done p => Raw.Program.compile (ε := ε) S T p
  | _, ss, .again i hi => resume ss i hi
  | _, _, .atom f args next => .atom f args (expand resume next)
  | _, _, .sum g args left right => .sum g args (expand resume left) (expand resume right)

end Step

/-- A one-step presentation of a family of native endpoints at every atomic
scope. Its local unfolding equations are checked separately. -/
structure System (c : α) where
  endpoint : ∀ {n : Nat}, (ss : Fin n → α) → State ss → Tm Empty (Φ ⊕ Ψ) n
  step : ∀ {n : Nat} (ss : Fin n → α) (i : State ss), Step S T (@rank) c (rank i) ss

section Expand

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- Compute a finite tree by well-founded recursion on the control rank. -/
noncomputable def System.expand (sys : System S T (@rank) c) {n : Nat}
    (ss : Fin n → α) (i : State ss) : Mixed.Program S T c ss :=
  Step.expand (ε := ε) S T (@rank) (fun ss j _ => sys.expand ss j) (sys.step ss i)
termination_by rank i

end Expand

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

/-- The certificate checks native typing at the original bound and compares
each endpoint with just its one-step tree, where repeats are still native
endpoints. It contains no expanded tree. -/
structure System.Checked (sys : System S T (@rank) c) (e : ε) : Prop where
  step_typed : ∀ {n : Nat} (ss : Fin n → α) (i : State ss), Step.WellTyped S T (@rank) e (sys.step ss i)
  endpoint_typed : ∀ {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α},
    Γ.Pure → (∀ j, (Γ.get j).1 = .base (ss j)) → ∀ (i : State ss),
    letI := SumCall.endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := SumCall.effects
    HasTypeEffect (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx (sys.endpoint ss i) (.base c) e
  unfold : ∀ {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α},
    Γ.Pure → (∀ j, (Γ.get j).1 = .base (ss j)) → ∀ (i : State ss),
    letI := SumCall.endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := SumCall.effects
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx (sys.endpoint ss i)
      (Step.native (ε := ε) S T (@rank) sys.endpoint (sys.step ss i)) (.base c)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Scoped

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked

universe u r

variable {α Φ Ψ ι : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) (rank : ι → Nat)
  {c : α}

/-- A scope-independent specialization of a ranked one-step tree. -/
abbrev Step := Scoped.Step S T (State := fun {_} _ => ι) (fun {_ _} => rank)

namespace Step

section Constructors

variable {S T rank}

@[match_pattern] abbrev done := @Scoped.Step.done α Φ Ψ S T (fun {_} _ => ι) (fun {_ _} => rank) c
@[match_pattern] abbrev again := @Scoped.Step.again α Φ Ψ S T (fun {_} _ => ι) (fun {_ _} => rank) c
@[match_pattern] abbrev atom := @Scoped.Step.atom α Φ Ψ S T (fun {_} _ => ι) (fun {_ _} => rank) c
@[match_pattern] abbrev sum := @Scoped.Step.sum α Φ Ψ S T (fun {_} _ => ι) (fun {_ _} => rank) c

end Constructors

abbrev WellTyped {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε] :=
  @Scoped.Step.WellTyped α Φ Ψ S T (fun {_} _ => ι) (fun {_ _} => rank) c (ε := ε)

noncomputable abbrev native {k : Nat} {ε : Type r} [HasEff Φ ε] [Bot ε]
    (resume : ∀ {n : Nat}, (Fin n → α) → ι → Tm Empty (Φ ⊕ Ψ) n)
    {n : Nat} {ss : Fin n → α} (p : Step S T rank c k ss) :=
  Scoped.Step.native (ε := ε) S T (fun {_ _} => rank) resume p

noncomputable abbrev expand {k : Nat} {ε : Type r} [HasEff Φ ε] [Bot ε]
    (resume : ∀ {n : Nat} (ss : Fin n → α) (i : ι), rank i < k → Mixed.Program S T c ss)
    {n : Nat} {ss : Fin n → α} (p : Step S T rank c k ss) :=
  Scoped.Step.expand (ε := ε) S T (fun {_ _} => rank) resume p

end Step

/-- A scope-independent specialization of a ranked system. -/
abbrev System := Scoped.System S T (State := fun {_} _ => ι) (fun {_ _} => rank)

section Projections

variable {S T rank}

abbrev System.mk := @Scoped.System.mk α Φ Ψ S T (fun {_} _ => ι) (fun {_ _} => rank) c
abbrev System.endpoint (sys : System S T rank c) := @Scoped.System.endpoint α Φ Ψ S T _ _ c sys
abbrev System.step (sys : System S T rank c) := @Scoped.System.step α Φ Ψ S T _ _ c sys

end Projections

section Expand

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

noncomputable abbrev System.expand (sys : System S T rank c) (i : ι)
    {n : Nat} (ss : Fin n → α) :=
  Scoped.System.expand (ε := ε) S T (fun {_ _} => rank) sys ss i

end Expand

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

abbrev System.Checked (sys : System S T rank c) (e : ε) :=
  Scoped.System.Checked S T (fun {_ _} => rank) sys e

section Checked

variable {S T rank} {sys : System S T rank c} {e : ε}

abbrev System.Checked.mk :=
  @Scoped.System.Checked.mk α Φ Ψ S T (fun {_} _ => ι) (fun {_ _} => rank) c ε _ _ _ _ _ sys e

abbrev System.Checked.step_typed (h : System.Checked S T rank sys e) :=
  @Scoped.System.Checked.step_typed α Φ Ψ S T _ _ c ε _ _ _ _ _ sys e h

abbrev System.Checked.endpoint_typed (h : System.Checked S T rank sys e) :=
  @Scoped.System.Checked.endpoint_typed α Φ Ψ S T _ _ c ε _ _ _ _ _ sys e h

abbrev System.Checked.unfold (h : System.Checked S T rank sys e) :=
  @Scoped.System.Checked.unfold α Φ Ψ S T _ _ c ε _ _ _ _ _ sys e h

end Checked

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked
