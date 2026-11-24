module

public import Silmaril.Logic.Operational.Machines.Thms
public import Silmaril.X86.RelIsa.Defs

/-!
# Operational view of relational x86

The live machine's register file and backing bytes are visible coordinates.
The control carrier retains the complete source state, including memory
permissions and any extension state. A distinguished stopped configuration
represents the existing `RelIsa.Res.stop` outcome.
-/

@[expose] public section

namespace Silmaril.X86.OperationalInstitution

open CategoryTheory Silmaril.Logic.Operational

/-- Use `none` for the stopped configuration. Addresses index the backing bytes. -/
def shape (σ : Type) : RegisterShape :=
  ⟨Option σ, Reg, Word, Nat, Silmaril.Process.Byte, Unit⟩

/-- Canonical register and byte views of a live or stopped configuration. -/
def encode {σ : Type} (V : RelIsa.Views σ) : Option σ → (shape σ).Config
  | none => ⟨none, fun _ => (0 : Word), fun _ => none⟩
  | some s => ⟨some s, (V.core s).regs, (V.mem s).bytes.get?⟩

/-- The existing relation restricted to live sources and canonical views.
A stopped configuration has no outgoing step. -/
def model {σ : Type} (A : RelIsa σ) :
    (RegisterShape.signatures.obj (shape σ)).Model
  | (src, _, dst) => match src.control with
    | none => False
    | some s =>
      src = encode A.toViews (some s) ∧ dst = encode A.toViews dst.control ∧
        A.live s ∧ A.step s (dst.control.elim .stop .ok)

/-- Package a landed relational model as a register system. -/
def system {σ : Type} (A : RelIsa σ) : RegisterSystem :=
  ⟨shape σ, model A⟩

end Silmaril.X86.OperationalInstitution
