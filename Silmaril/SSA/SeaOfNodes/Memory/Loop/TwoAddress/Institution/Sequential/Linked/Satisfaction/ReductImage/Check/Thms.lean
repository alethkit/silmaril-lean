module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Lift
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Coverage

/-! Exact executable coverage and lifts for canonical typed valuations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage

open CategoryTheory
open RVSDG (Port Tuple)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q : EntrySignature} {cells : Nat}

theorem admitsInput_iff (cells : Nat) (args : List ValueSort) :
    admitsInput cells args = true ↔ Nonempty (Tuple (Val cells) args) :=
  Proofs.admitsInput_iff cells args

theorem admitsInput_zero_iff (args : List ValueSort) :
    admitsInput 0 args = true ↔ ValueSort.address ∉ args :=
  Proofs.admitsInput_zero_iff args

theorem checkNoIdentification_iff (h : P ⟶ Q) (sort : ValueSort) :
    checkNoIdentification h sort = true ↔ Function.Injective (fun port : Port P.args sort => h.port port) :=
  Proofs.checkNoIdentification_iff h sort

theorem checkFibres_iff (h : P ⟶ Q) (input : Tuple (Val cells) P.args) :
    checkFibres h input = true ↔ FibreConsistent h input :=
  Proofs.checkFibres_iff h input

/-- A lift exists exactly when the target tuple is inhabited and every
pair of source ports with the same image agrees on its value. -/
theorem inReductImage_iff (h : P ⟶ Q) (input : Tuple (Val cells) P.args) :
    InReductImage h input ↔ Nonempty (Tuple (Val cells) Q.args) ∧ FibreConsistent h input :=
  Proofs.inReductImage_iff h input

theorem liftInput?_sound (h : P ⟶ Q) {input : Tuple (Val cells) P.args} {target : Tuple (Val cells) Q.args}
    (lifted : liftInput? h input = some target) : reduct h ⟨cells, target⟩ = ⟨cells, input⟩ :=
  Proofs.liftInput?_sound h lifted

theorem liftInput?_isSome_iff (h : P ⟶ Q) (input : Tuple (Val cells) P.args) :
    (liftInput? h input).isSome = true ↔ InReductImage h input :=
  Proofs.liftInput?_isSome_iff h input

theorem checkCoverage_iff (h : P ⟶ Q) (cells : Nat) :
    checkCoverage h cells = true ↔ ∀ input : Tuple (Val cells) P.args, InReductImage h input :=
  Proofs.checkCoverage_iff h cells

/-- At one cell only words can distinguish identified source ports. -/
theorem checkCoverage_one (h : P ⟶ Q) : checkCoverage h 1 = checkNoIdentification h .word :=
  Proofs.checkCoverage_one h

/-- With at least two cells, the reduct is surjective exactly when the
capture map is injective within each sort. -/
theorem checkCoverage_of_two_le (h : P ⟶ Q) (two : 2 ≤ cells) :
    checkCoverage h cells = (checkNoIdentification h .word && checkNoIdentification h .address) :=
  Proofs.checkCoverage_of_two_le h two

theorem checkExpansive_iff (h : P ⟶ Q) :
    checkExpansive h = true ↔ ∀ cells (input : Tuple (Val cells) P.args), InReductImage h input :=
  Proofs.checkExpansive_iff h

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage
