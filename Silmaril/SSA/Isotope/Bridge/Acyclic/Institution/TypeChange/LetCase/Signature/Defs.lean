module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.LetCase.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TypeChangeCaseOperation

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory
open Morphism (SignatureMap)
open Theory (TypingIndex)
open Isotope.LetCase.LocallyNameless
open Silmaril.Logic.Metatheory.TheoryModel

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "Δ₀" => (Ctx.nil : Ctx Empty υ)
local notation "S₀" => Models.signature P.Instr Γ₀
local notation "T₀" => Models.signature Q.Instr Δ₀

/-- Operation signature translation for the actual exact LetCase presentation.
Result sorts and argument sorts use the same image of the typing index. -/
def typeCaseSignatureHom : Signature.Hom S₀ T₀ where
  sort := mapTypingIndex g
  op o := castOp T₀ (by exact mappedCaseOp_index g o) (mappedCaseOp g o).2
  arg o := finCongr (by exact (arity_castOp T₀ _ _).trans (mappedCaseOp_arity g o))
  argSort o j := by
    exact (mappedCaseOp_args g o (Fin.cast (arity_castOp T₀ _ _) j)).trans
      (argSort_castOp T₀ _ _ j).symm

/-- View the operation map as a map of the actual presented syntaxes. -/
abbrev typeCaseHom : LetCase.presObj Γ₀ P ⟶ LetCase.presObj Δ₀ Q :=
  typeCaseSignatureHom g

end Silmaril.Isotope.Institution.Acyclic
