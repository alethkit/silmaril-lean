module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.FixedCapCategory.Defs
import Mathlib.Data.List.OfFn

public section

namespace Silmaril.RuntimeWires.Proofs.CapRecoordination

open ProgressiveGraph

universe u
variable {O : Type u} {a b : CapProfile O}

theorem same_size (h : List.ofFn a.label = List.ofFn b.label) : a.size = b.size := by
  simpa only [List.length_ofFn] using congrArg List.length h

theorem same_label (h : List.ofFn a.label = List.ofFn b.label) (i : Fin a.size) :
    a.label i = b.label (i.cast (same_size h)) := by
  obtain ⟨_, labels⟩ := Fin.sigma_eq_iff_eq_comp_cast.mp (List.ofFn_inj'.mp h)
  exact congrFun labels i

end Silmaril.RuntimeWires.Proofs.CapRecoordination
