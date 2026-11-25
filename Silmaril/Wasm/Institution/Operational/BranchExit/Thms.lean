module

public import Silmaril.Wasm.Institution.Operational.BranchExit.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.BranchExit

open Silmaril.Semantics.SOS

theorem fact {ty : Option NumType} {a b : State} (h : Outcome ty a b) : Edge ty a b :=
  Derives.apply (R := (presentation ty).rules) (r := ⟨[], (a, b)⟩) ⟨rfl, h⟩ (fun _ h => nomatch h)

theorem invert {ty : Option NumType} {a b : State} (h : Edge ty a b) : Outcome ty a b :=
  Derives.least (M := fun j => Outcome ty j.1 j.2) h (fun _ hr _ => hr.2)

theorem closed {ty : Option NumType} {a b : State} (edge : Edge ty a b) (guard : Admitted ty a) :
    Admitted ty b := by
  cases invert edge <;> exact guard

end Silmaril.Wasm.Institution.Operational.BranchExit
