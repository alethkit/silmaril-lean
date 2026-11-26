module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Thms

open CategoryTheory
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.Institution Silmaril.Isotope.Institution.Refinement
open Silmaril.Isotope.Theory (TypingIndex)

namespace IsotopeUndefinedBehaviourTests

private abbrev τ := Ty Empty
private def alphabet : InstrSig τ Bool where
  Instr := Empty
  hasTy := ⟨Empty.elim, Empty.elim⟩
  hasEff := ⟨Empty.elim⟩

private abbrev Γ : Ctx Empty τ := .nil
private abbrev closed : TypingIndex τ := ⟨0, .nil, unit⟩
private abbrev underBinder : TypingIndex τ := ⟨1, .snoc .nil unit, unit⟩

-- The native extension records the declared effect at every result type.
example (A : τ) :
    let P := UB.dialect alphabet true
    @instrEff P.Instr Bool P.hasEff (.inr A) = true := rfl

-- Both layers of the primitive extension collapse to the same generator.
example (A : τ) :
    let m := UB.dialectMonad (τ := τ) true
    InstrSig.Hom.instr (m.μ.app alphabet) (.inl (.inr A)) =
      InstrSig.Hom.instr (m.μ.app alphabet) (.inr A) := rfl

private def letUB : UB.LetCase.Explicit alphabet Γ closed :=
  let S := (casePSig alphabet.Instr Γ).sig
  let o : S.Op closed := LetCase.LocallyNameless.Models.Operation.let₁ unit unit
  UB.Expr.node o (Fin.cases (motive := fun j => UB.Expr S (S.argSort o j))
    (UB.Expr.node LetCase.LocallyNameless.Models.Operation.unit (fun j => Fin.elim0 j))
    (fun _ => UB.Expr.ub))

-- The native spelling remains canonical inside the binder.
example : (UB.LetCase.typedEquiv alphabet true Γ closed letUB).val.1 =
    .let₁ .unit (.op (.inr unit) .unit) := rfl

example :
    (UB.LetCase.typedEquiv alphabet true Γ closed).symm
      (UB.LetCase.typedEquiv alphabet true Γ closed letUB) = letUB :=
  Equiv.symm_apply_apply _ _

private noncomputable def caseSpec : UB.Specification.{0,0} :=
  letI := alphabet.hasTy
  letI := alphabet.hasEff
  (Silmaril.Logic.Institution.Theory.toSpec institution).obj
    (caseTheory (Φ := alphabet.Instr) false Γ (fun _ _ _ _ => False))

-- An open judgment sort has a greatest class in the initial ordered model.
example (x : (UB.Specification.syntacticModel caseSpec).algebra.Carrier underBinder) :
    @LE.le _ ((UB.Specification.syntacticModel caseSpec).algebra.order underBinder).toLE x
      (UB.Specification.ubClass caseSpec underBinder) :=
  UB.Specification.initial_le_ub caseSpec underBinder x

-- The multiplication really identifies the two symbols at an open sort.
example :
    let f := (UB.Specification.multiply caseSpec).sig
    (PSig.toSig f).op (i := underBinder) (some none) = (PSig.toSig f).op (i := underBinder) none :=
  rfl

#print axioms UB.Specification.monad
#print axioms UB.Specification.initial_le_ub
#print axioms UB.LetCase.typedEquiv

end IsotopeUndefinedBehaviourTests
