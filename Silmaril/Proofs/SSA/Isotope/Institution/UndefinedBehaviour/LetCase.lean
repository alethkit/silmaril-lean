module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Defs

public section

namespace Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase

open CategoryTheory
open Silmaril.Isotope
open Silmaril.Isotope.Institution.Refinement.UB
open Silmaril.Isotope.Institution.Refinement.UB.LetCase
open Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.LetCase.LocallyNameless
open Silmaril.Isotope.Theory (TypingIndex)

attribute [local instance] dialectTyping

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν]
variable {P : Institution.InstrSig τ ε} {e : ε} {Γ : Ctx ν τ} {i : TypingIndex τ}

theorem encode_canonical (t : Explicit P Γ i) : Canonical P e Γ (encode P e Γ t) := by
  induction t with
  | ub => exact .ub _
  | node o args ih => exact .op o _ ih

theorem decode_encode (t : Explicit P Γ i) :
    decode P e Γ ⟨encode P e Γ t, encode_canonical t⟩ = t := by
  let φ := Models.fold (decodeAlgebra P e Γ)
  change φ.map (encode P e Γ t) = t
  induction t with
  | ub => rfl
  | node o args ih =>
    change φ.map ((oldOps P e Γ).op o (fun j => encode P e Γ (args j))) = Expr.node o args
    let f := Institution.LetCase.sigHom Γ (includeDialect P e)
    change φ.map ((Silmaril.Isotope.Institution.Refinement.casePSig (dialect P e).Instr Γ).syn.op
      (f.op o) _) = _
    rw [φ.comm]
    cases o <;> simp only [f, Institution.LetCase.sigHom, Institution.LetCase.opMap,
      Institution.LetCase.argMap, decodeAlgebra,
      includeDialect, Institution.castOp]
    all_goals apply congrArg; funext j; exact ih j

theorem canonical_surjective (t : Native P e Γ i) (h : Canonical P e Γ t) :
    ∃ a : Explicit P Γ i, encode P e Γ a = t := by
  induction h with
  | ub i => exact ⟨.ub, rfl⟩
  | op o args h ih =>
    choose a ha using ih
    exact ⟨.node o a, congrArg ((oldOps P e Γ).op o) (funext ha)⟩

end Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetCase
