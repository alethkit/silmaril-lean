module

public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms
public import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Interpretation

public section

namespace Silmaril.RuntimeWires.Proofs.SlicedCompleteness.Regression

open CategoryTheory Silmaril.RuntimeWires.Sliced

private abbrev scalarSignature : Signature PEmpty.{1} where
  Edge := Bool
  source _ := []
  target _ := []

private abbrev scalarTerm (label : Bool) : Diagram scalarSignature [] [] :=
  .gen label

private theorem leftFirst (f g : Diagram scalarSignature [] []) :
    Diagram.Congruence (noEquations scalarSignature) (.comp f g) (.tensor f g) :=
  .trans (.comp (.symm (.tensor_unit_right f)) (.symm (.tensor_unit_left g)))
    (.trans (.symm (.tensor_comp f (.id []) (.id []) g)) (.tensor (.comp_id f) (.id_comp g)))

private theorem rightFirst (f g : Diagram scalarSignature [] []) :
    Diagram.Congruence (noEquations scalarSignature) (.comp g f) (.tensor f g) :=
  .trans (.comp (.symm (.tensor_unit_left g)) (.symm (.tensor_unit_right f)))
    (.trans (.symm (.tensor_comp (.id []) f g (.id []))) (.tensor (.id_comp f) (.comp_id g)))

/-- Two distinct generators with empty inputs and outputs can be rescheduled
using the original seam moves. The test obtains the seam witness by reflection. -/
example : Sheet.SeamEquivalent
    ((Sheet.generator (S := scalarSignature) false).thenDo (Sheet.generator true))
    ((Sheet.generator (S := scalarSignature) true).thenDo (Sheet.generator false)) := by
  let f := scalarTerm false
  let g := scalarTerm true
  let E : Diagram.Equations scalarSignature := noEquations scalarSignature
  let A : Diagram.Presented scalarSignature E := ⟨[]⟩
  have e : Diagram.Presented.ofTerm (A := A) (B := A) (.comp f g) =
      Diagram.Presented.ofTerm (A := A) (B := A) (.comp g f) :=
    Quotient.sound (.trans (leftFirst f g) (.symm (rightFirst f g)))
  apply Sheet.denote_eq_iff.mp
  exact (denote_encode E (.comp f g)).trans (e.trans (denote_encode E (.comp g f)).symm)

end Silmaril.RuntimeWires.Proofs.SlicedCompleteness.Regression
