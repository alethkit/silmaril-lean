module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked

/-! # Ranked native expansion and original-bound comparison with raw trees -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked

universe u r

/-- One step of the computed expansion retains the recursive calls only at
the strictly smaller repeat sites. -/
theorem System.expand_step {α Φ Ψ ι : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
    (rank : ι → Nat) {c : α} {ε : Type r} [HasEff Φ ε] [Bot ε]
    (sys : System S T rank c) (i : ι) {n : Nat} (ss : Fin n → α) :
    System.expand (ε := ε) S T rank sys i ss =
      Step.expand (ε := ε) S T rank
        (fun slots j _ => System.expand (ε := ε) S T rank sys j slots) (sys.step ss i) :=
  System.expand.eq_def S T rank sys i ss

variable {α Φ Ψ ι : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) (rank : ι → Nat)
  {c : α} {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

/-- The computed finite tree is well typed at the supplied bound. -/
theorem expand_typed (sys : System S T rank c) (i : ι) {n : Nat} (ss : Fin n → α) (e : ε)
    (h : System.Checked S T rank sys e) :
    Mixed.Program.WellTyped S T e (System.expand (ε := ε) S T rank sys i ss) :=
  Proofs.expand_typed S T rank sys i ss e h

/-- The native endpoint and its computed expansion agree and retain the bound. -/
theorem expand_native (sys : System S T rank c) (e : ε)
    (h : System.Checked S T rank sys e) (i : ι)
    {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ j, (Γ.get j).1 = .base (ss j)) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    HasTypeEffect Γ₀ Γ.toBoundCtx (sys.endpoint ss i) (.base c) e ∧
      HasTypeEffect Γ₀ Γ.toBoundCtx (System.expand (ε := ε) S T rank sys i ss).native (.base c) e ∧
      AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (sys.endpoint ss i)
        (System.expand (ε := ε) S T rank sys i ss).native (.base c) :=
  Proofs.expand_native S T rank sys e h i hΓ hs

variable [DecidableEq α]

/-- Compare a ranked native endpoint to a raw mixed endpoint. The source
equality compares the computed loop-free expansion to the raw endpoint. -/
theorem raw_endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (sys : System S T rank c) (e : ε) (h : System.Checked S T rank sys e) (i : ι)
    {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ j, (Γ.get j).1 = .base (ss j))
    (q : Raw.Program S T c ss) (hq : Raw.Program.WellTyped S T e q)
    {t : Tm Empty (Φ ⊕ Ψ) Γ.length} (ht : q.source.toLetIter Γ.length = some t) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (sys.endpoint ss i) t (.base c) ↔
      Eqv Γ (.base c) e (System.expand (ε := ε) S T rank sys i ss).source q.source :=
  Proofs.raw_endpoint_reflection S T rank visible sys e h i hΓ hs q hq ht


/-- Compare two independently ranked native endpoints by their computed
source expansions at the same effect bound. -/
theorem endpoint_reflection {κ : Type u} (rank' : κ → Nat)
    (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) (e : ε)
    (sys : System S T rank c) (h : System.Checked S T rank sys e) (i : ι)
    (sys' : System S T rank' c) (h' : System.Checked S T rank' sys' e) (i' : κ)
    {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ j, (Γ.get j).1 = .base (ss j)) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (sys.endpoint ss i) (sys'.endpoint ss i') (.base c) ↔
      Eqv Γ (.base c) e (System.expand (ε := ε) S T rank sys i ss).source
        (System.expand (ε := ε) S T rank' sys' i' ss).source :=
  Proofs.endpoint_reflection S T rank rank' visible e sys h i sys' h' i' hΓ hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked
