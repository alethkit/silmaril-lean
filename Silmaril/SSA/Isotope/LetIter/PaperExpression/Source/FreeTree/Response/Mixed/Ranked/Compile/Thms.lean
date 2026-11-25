module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile

/-! # Native unfolding and fixed-bound reflection for compiled controllers -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {a a' c : α} {k k' : Nat} {ε : Type r}
  [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

/-- Typed fixpoint unfolding picks the current state body and dispatches its
returns and repeats under the request binders. This uses exact native equality. -/
theorem Controller.unfold_step {n : Nat} {ss : Fin n → α} {β : BoundCtx (Ty α) n}
    (hs : ∀ j, β.get j = .base (ss j)) (p : Controller S T a c k) (e : ε)
    (hp : ∀ j, Body.WellTyped S T e (p j)) (i : Entry S ε a k ss) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    LocallyNameless.Equiv (⊥ : ε) Γ₀ β (p.loop S T i)
      (Scoped.Step.native (ε := ε) S T (@entryRank _ _ S a k ε _ _)
        (p.system S T e hp).endpoint ((p.system S T e hp).step ss i)) (.base c) :=
  Proofs.unfold S T hs p e hp i

/-- The compiler constructs a checked ranked system from body typing and an
iteration-closed effect bound. The local native equations are derived. -/
theorem Controller.checked (p : Controller S T a c k) (e : ε) (he : IsIterative e)
    (hp : ∀ j, Body.WellTyped S T e (p j)) :
    Scoped.System.Checked S T (@entryRank _ _ S a k ε _ _) (p.system S T e hp) e :=
  Proofs.checked S T p e he hp

variable [DecidableEq α]

/-- Compare the two compiled native loops with their finite source renderings
at the supplied effect bound. -/
theorem endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) (e : ε) (he : IsIterative e)
    (p : Controller S T a c k) (hp : ∀ j, Body.WellTyped S T e (p j))
    (q : Controller S T a' c k') (hq : ∀ j, Body.WellTyped S T e (q j))
    {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ j, (Γ.get j).1 = .base (ss j)) (i : Entry S ε a k ss) (j : Entry S ε a' k' ss) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (p.loop S T i) (q.loop S T j) (.base c) ↔
      Eqv Γ (.base c) e (p.expansion S T e hp i).source (q.expansion S T e hq j).source :=
  Scoped.endpoint_reflection S T (@entryRank _ _ S a k ε _ _) (@entryRank _ _ S a' k' ε _ _)
    visible e _ (p.checked S T e he hp) _ (q.checked S T e he hq) i j hΓ hs

/-- Compare one compiled native loop with the lowering of a raw mixed
endpoint at the supplied effect bound. -/
theorem raw_endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) (e : ε) (he : IsIterative e)
    (p : Controller S T a c k) (hp : ∀ j, Body.WellTyped S T e (p j))
    {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ j, (Γ.get j).1 = .base (ss j)) (i : Entry S ε a k ss)
    (q : Raw.Program S T c ss) (hq : q.WellTyped S T e)
    {t : Term (Φ := Φ) (Ψ := Ψ) Γ.length} (ht : q.source.toLetIter Γ.length = some t) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (p.loop S T i) t (.base c) ↔
      Eqv Γ (.base c) e (p.expansion S T e hp i).source q.source :=
  Scoped.raw_endpoint_reflection S T (@entryRank _ _ S a k ε _ _) visible _ _ (p.checked S T e he hp)
    i hΓ hs q hq ht

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile
