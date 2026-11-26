module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Defs
public import Silmaril.Raw.SSA.Isotope.Institution.SigHomExt

/-! # Relabelling of the exact LetCase operation symbols and their sorts -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open Morphism (SignatureMap)
open Theory (TypingIndex)
open Isotope.LetCase.LocallyNameless
open Silmaril.Logic.Metatheory.TheoryModel

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "Δ₀" => (Ctx.nil : Ctx Empty υ)

/-- The mapped constructor with its native result sort, before transporting
along type-former preservation. -/
def mappedCaseOp : {i : TypingIndex τ} → Models.Operation (Φ := P.Instr) Γ₀ i →
    Σ j, Models.Operation (Φ := Q.Instr) Δ₀ j
  | _, .fv (x := x) _ => x.elim
  | _, .bv (β := β) k => ⟨_, .bv (β := β.mapTypes g.ty) k⟩
  | _, .op (β := β) f => ⟨_, .op (β := β.mapTypes g.ty) (g.instr f)⟩
  | _, .let₁ (β := β) A B => ⟨_, .let₁ (β := β.mapTypes g.ty) (g.ty A) (g.ty B)⟩
  | _, .unit (β := β) => ⟨_, .unit (β := β.mapTypes g.ty)⟩
  | _, .pair (β := β) A B => ⟨_, .pair (β := β.mapTypes g.ty) (g.ty A) (g.ty B)⟩
  | _, .let₂ (β := β) A B C => ⟨_, .let₂ (β := β.mapTypes g.ty) (g.ty A) (g.ty B) (g.ty C)⟩
  | _, .inl (β := β) A B => ⟨_, .inl (β := β.mapTypes g.ty) (g.ty A) (g.ty B)⟩
  | _, .inr (β := β) A B => ⟨_, .inr (β := β.mapTypes g.ty) (g.ty A) (g.ty B)⟩
  | _, .case (β := β) A B C => ⟨_, .case (β := β.mapTypes g.ty) (g.ty A) (g.ty B) (g.ty C)⟩
  | _, .abort (β := β) C => ⟨_, .abort (β := β.mapTypes g.ty) (g.ty C)⟩

end Silmaril.Isotope.Institution.Acyclic
