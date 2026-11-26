module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.SSA.Isotope.LetIter.AbortSequence.Normalization.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Observation

/-! # Recovering feedback step correspondence from visible observations -/

public section

open Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback

universe u v

variable {α Φ : Type u} [HasTy Φ (Ty α)] {V : α → Type u} {f : Φ}
  {S T B : Type v} {L : Machine V f S B} {R : Machine V f T B}

theorem Machine.run_unfold (M : Machine V f S B) (s : S) :
    M.run s = ITree.vis (.call f (M.request s))
      (fun r => Sum.elim ITree.ret M.run (M.reply s r)) :=
  Proofs.run_unfold M s

/-- A comparison at one pair of states matches the request, return values,
and observations at the related repeat states. -/
theorem related_step {s : S} {t : T} (eq : L.run s = R.run t) :
    L.request s = R.request t ∧
      ∀ r, match L.reply s r, R.reply t r with
      | .inl a, .inl b => a = b
      | .inr s', .inr t' => L.run s' = R.run t'
      | _, _ => False :=
  Proofs.related_step eq

theorem runs_eq {h : S → T} (comm : Commutes L R h) : ∀ s, L.run s = R.run (h s) :=
  Proofs.runs_eq comm

/-- Pointwise observations recover the typed semantic square when right
requests distinguish states. Uniformity gives the converse. -/
theorem runs_eq_iff {h : S → T} (separates : Function.Injective R.request) :
    (∀ s, L.run s = R.run (h s)) ↔ Commutes L R h :=
  Proofs.runs_eq_iff separates

/-- Coverage of all left states recovers a semantic state map. -/
theorem exists_commutes (separates : Function.Injective R.request)
    (covers : ∀ s, ∃ t, L.run s = R.run t) : ∃ h, Commutes L R h :=
  Proofs.exists_commutes separates covers

/-- Initial equality recovers a total semantic square if every left state
is reachable by repeat replies and the right requests distinguish states. -/
theorem exists_commutes_of_initial {s₀ : S} {t₀ : T}
    (separates : Function.Injective R.request) (reaches : ∀ s, L.Reaches s₀ s)
    (initial : L.run s₀ = R.run t₀) : ∃ h, Commutes L R h ∧ h s₀ = t₀ :=
  Proofs.exists_commutes_of_initial separates reaches initial

section Replay

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm HasType AbortEquiv Pure)

variable {ε : Type v} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx (Ty α) ε} {A A' C : Ty α} {e : ε}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "β" => Γ.toBoundCtx

/-- Lower a typed, loop-free source square and replay it with native pure
uniformity. The source equation compares the square's step endpoints. -/
theorem replay_written_square
    {a : Tm Empty Φ Γ.length} {h b b' : Tm Empty Φ (Γ.length + 1)}
    {p q : Expr Φ}
    (ha : HasType Φ Γ₀ β a A) (hh : HasType Φ Γ₀ (Γ.toBoundCtx.snoc A) h A')
    (hp : Pure (⊥ : ε) h)
    (hb : HasType Φ Γ₀ (Γ.toBoundCtx.snoc A) b (.coprod C A))
    (hb' : HasType Φ Γ₀ (Γ.toBoundCtx.snoc A') b' (.coprod C A'))
    (hl : p.toLetIter (Γ.length + 1) = some (.case b (.inl (.bv 0)) (.inr (Tm.underBinder h))))
    (hr : q.toLetIter (Γ.length + 1) = some (Tm.instantiate (Tm.underBinder b') h))
    (eq : Source.Eqv ((A, ⊥) :: Γ) (.coprod C A') e p q) :
    AbortEquiv (⊥ : ε) Γ₀ β (.iter a b) (.iter (.let₁ a h) b') C :=
  LocallyNameless.AbortNormalization.repaired_uniformity ha hh hp hb hb' (eq.toLetIter hl hr)

end Replay

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback
