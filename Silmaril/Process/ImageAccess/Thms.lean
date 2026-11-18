module

public import Silmaril.Process.ImageAccess.Defs
import Silmaril.Proofs.Process.ImageAccess.Basic

@[expose] public section

namespace Silmaril.Process.ImageAccess

theorem Reader.Refines.trans {complex middle simple : Reader}
    (outer : Reader.Refines complex middle) (inner : Reader.Refines middle simple) :
    Reader.Refines complex simple := fun request bytes answer => outer request bytes (inner request bytes answer)

theorem Program.wp_iff_run {α : Type} {reader : Reader} {post : α → Prop} (program : Program α) :
    program.wp reader post ↔ ∃ value, program.run reader = .ok value ∧ post value :=
  Proofs.Process.ImageAccess.wp_iff_run program

theorem Program.wp_transfer {α : Type} {target source : Reader} {post : α → Prop}
    (refines : Reader.Refines target source) (program : Program α) :
    program.wp source post → program.wp target post :=
  Proofs.Process.ImageAccess.wp_transfer refines program

/-- Lifting an ownership restriction on the same snapshot preserves every successful reply. -/
theorem Image.full_refines_owned (memory : Memory) (owns : Read → Bool) (outside : Outside) :
    Reader.Refines (Image.full memory).localReader (Image.owned memory owns outside).localReader :=
  Proofs.Process.ImageAccess.full_refines_owned memory owns outside

end Silmaril.Process.ImageAccess
