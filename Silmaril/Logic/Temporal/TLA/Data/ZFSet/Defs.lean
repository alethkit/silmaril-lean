module

public import Mathlib.SetTheory.ZFC.Basic
public import Silmaril.Logic.Temporal.TLA.Data.Defs

/-! # Realization in Mathlib's extensional ZF sets -/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Data

universe u

/-- Interpret all values as `ZFSet`. A mapped set is indexed by the small type of members
of its bound, and the caller supplies the value of choice on an unsatisfiable predicate. -/
noncomputable def zfSetModel (fallback : ZFSet.{u}) : Model ZFSet.{u} where
  mem := fun x s => x ∈ s
  empty := ∅
  insert := Insert.insert
  sep := fun s p => ZFSet.sep p s
  image := fun s f => ZFSet.range (fun x : s => f x.val)
  sUnion := ZFSet.sUnion
  powerset := ZFSet.powerset
  choice := ChoicePolicy.classical fallback
  ext := ZFSet.ext
  notMem_empty := ZFSet.notMem_empty
  mem_insert := ZFSet.mem_insert_iff
  mem_sep := ZFSet.mem_sep
  mem_image := by
    intro x s f
    exact ZFSet.mem_range.trans
      ⟨fun ⟨⟨y, hy⟩, h⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨⟨y, hy⟩, h⟩⟩
  mem_sUnion := ZFSet.mem_sUnion
  mem_powerset := ZFSet.mem_powerset

end Silmaril.Logic.Temporal.TLA.Data
