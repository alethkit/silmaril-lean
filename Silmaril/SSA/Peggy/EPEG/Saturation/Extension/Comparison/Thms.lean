module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Defs
public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Thms
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Embedding
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.ZeroSample

public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension

open PEG

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n k j l : Nat}
variable {small : State P params results n l} {large : State P params results k l}
variable {larger : State P params results j l}
variable {g : Graph P params results n l} {site : Fin n} {zero : P [] .count}

def Embedding.refl (state : State P params results n l) : Embedding state state :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.refl state

def Embedding.trans (first : Embedding small large) (second : Embedding large larger) :
    Embedding small larger :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.trans first second

theorem Comparable.refl (state : Output P params results l) : Comparable state state :=
  ⟨Embedding.refl state.2⟩

theorem Comparable.trans {a b c : Output P params results l}
    (first : Comparable a b) (second : Comparable b c) : Comparable a c := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨first.trans second⟩

@[simp] theorem Embedding.append_address_old (e : Embedding small large) (row : Row small.graph) (i : Fin n) :
    (e.appendVertices row).address i.castSucc = (e.vertices.address i).castSucc :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.append_address_old e row i

@[simp] theorem Embedding.append_address_fresh (e : Embedding small large) (row : Row small.graph) :
    (e.appendVertices row).address (Fin.last n) = Fin.last k :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.append_address_fresh e row

/-- Equation (4.1) as a concrete state embedding for any append receipt. -/
def Step.embedding (step : Step small) : Embedding small step.apply :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.step step

theorem ZeroSample.transport_row (e : Embedding small large) (found : ZeroSample small.graph site zero) :
    (found.transport e).row = e.mapRow found.row :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.transport_row e found

theorem ZeroSample.matchAt_of_witness [DecidableEq (P [] .count)] (found : ZeroSample g site zero) :
    ZeroSample.matchAt site zero = some found :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.matchAt_of_witness found

/-- The executable matcher accepts the mapped site with the transported witness. -/
theorem ZeroSample.matchAt_transport [DecidableEq (P [] .count)] (e : Embedding small large)
    (found : ZeroSample small.graph site zero) :
    ZeroSample.matchAt (e.vertices.address site) zero = some (found.transport e) :=
  (found.transport e).matchAt_of_witness

/-- Compare the actual outputs of the two one-merge-fuel runs. Map the fresh
row to the fresh row even when a duplicate is already present. -/
theorem ZeroSample.simulate (e : Embedding small large) (found : ZeroSample small.graph site zero) :
    ∃ mapped : Embedding found.step.apply (found.transport e).step.apply,
      ∀ i, mapped.vertices.address i = (e.appendVertices found.row).address i :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.simulate e found

theorem ZeroSampleAnalysis.inflationary (zero : P [] .count) :
    Inflationary (params := params) (results := results) (l := l) (ZeroSampleAnalysis zero) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.zeroSample_inflationary zero

/-- Equation (4.2) for the zero-sample analysis under fresh append. -/
theorem ZeroSampleAnalysis.monotone (zero : P [] .count) :
    MonotoneAnalysis (params := params) (results := results) (l := l) (ZeroSampleAnalysis zero) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Comparison.zeroSample_monotone zero

/-- Equation (4.3). Delaying the first analysis uses its own monotonicity
and only the inflationary property of the intervening analysis. -/
theorem delayed_step {a b : Analysis P params results l}
    (monotone : MonotoneAnalysis a) (inflationary : Inflationary b)
    {source first intervening : Output P params results l}
    (left : a source first) (right : b source intervening) :
    ∃ delayed, a intervening delayed ∧ Comparable first delayed :=
  monotone (inflationary right) left

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension
