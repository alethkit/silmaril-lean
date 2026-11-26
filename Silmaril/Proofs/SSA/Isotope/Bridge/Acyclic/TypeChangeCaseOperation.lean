module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.LetCase.Defs

public section

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

theorem mappedCaseOp_index {i : TypingIndex τ} (o : (S₀).Op i) :
    (mappedCaseOp g o).1 = mapTypingIndex g i := by
  cases o with
  | @fv n β x A hp => exact x.elim
  | bv k => simp [mappedCaseOp, mapTypingIndex]
  | op f => simp [mappedCaseOp, mapTypingIndex, g.target f]
  | unit => simp [mappedCaseOp, mapTypingIndex]
  | pair A B => simp [mappedCaseOp, mapTypingIndex]
  | inl A B => simp [mappedCaseOp, mapTypingIndex]
  | inr A B => simp [mappedCaseOp, mapTypingIndex]
  | _ => rfl

omit [g.PreservesProducts] [g.PreservesSums] in
theorem mappedCaseOp_arity {i : TypingIndex τ} (o : (S₀).Op i) :
    (T₀).arity (mappedCaseOp g o).2 = (S₀).arity o := by
  cases o with
  | @fv n β x A hp => exact x.elim
  | _ => rfl

theorem mappedCaseOp_args {i : TypingIndex τ} (o : (S₀).Op i)
    (j : Fin ((T₀).arity (mappedCaseOp g o).2)) :
    mapTypingIndex g ((S₀).argSort o (Fin.cast (mappedCaseOp_arity g o) j)) =
      (T₀).argSort (mappedCaseOp g o).2 j := by
  cases o with
  | @fv n β x A hp => exact x.elim
  | bv k => exact Fin.elim0 j
  | unit => exact Fin.elim0 j
  | op f => simp [mappedCaseOp, mapTypingIndex, g.source f]
  | abort A => simp [mappedCaseOp, mapTypingIndex]
  | let₁ A B => fin_cases j <;> rfl
  | let₂ A B D => fin_cases j <;> first | rfl | simp [mappedCaseOp, mapTypingIndex, Models.Operation.argSort]
  | pair A B => fin_cases j <;> rfl
  | inl A B => rfl
  | inr A B => rfl
  | case A B D => fin_cases j <;> first | rfl | simp [mappedCaseOp, mapTypingIndex, Models.Operation.argSort]

end Silmaril.Isotope.Institution.Acyclic
