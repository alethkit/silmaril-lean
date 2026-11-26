module

public import Silmaril.SSA.SeaOfNodes.Quads.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Correctness

/-! # Reaching definitions and exact returned-value agreement for ordered quads -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads

open RVSDG (Port PortType Tuple Origin Wires Locals)
open Diamond (Ty ValueSort Signature Model Val dataPorts)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out result : ValueSort Data}
variable {args : List (Ty Data)} {past : List (List (Ty Data))}

/-- Before any assignment, a use names the corresponding input. -/
theorem initial_get {t : Ty Data} (port : Port (dataPorts regs) t) :
    (initial regs).get port = .arg port :=
  Proofs.initial_get port

/-- Appending a producer does not renumber any earlier producer. -/
theorem keep_producer {added : List (Ty Data)} {t : Ty Data} (origin : Origin args past t) :
    (keep (added := added) origin).producer = origin.producer := by
  cases origin <;> rfl

/-- A write makes this instruction's result the reaching definition of its destination. -/
theorem rebind_same (current : Wires args past (dataPorts regs))
    (dest : Port (dataPorts regs) (.value result)) :
    (rebind current dest).get dest = .output (Diamond.lastIndex [.value result] past)
      (Diamond.lastPort .head past) :=
  Proofs.rebind_same current dest

/-- Overwriting one register preserves the reaching definition of every other register. -/
theorem rebind_other (current : Wires args past (dataPorts regs))
    (dest : Port (dataPorts regs) (.value result)) {t : Ty Data}
    (source : Port (dataPorts regs) t) (different : slot source ≠ slot dest) :
    (rebind current dest).get source = keep (current.get source) :=
  Proofs.rebind_other current dest source different

/-- Running the lowered graph returns exactly the value of ordered register execution. -/
theorem Code.lower_run (code : Code Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    code.lower.run m.toRVSDG entry = .cons (code.eval m entry) .nil :=
  Proofs.lower_run code m entry

/-- The straight-line evaluator also agrees under a typed map into an open graph prefix. -/
theorem Code.lowerFrom_eval (code : Code Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (code.lowerFrom current).eval m.toRVSDG entry locals =
      .cons (code.eval m (current.read entry locals)) .nil :=
  Proofs.lowerFrom_eval code m entry locals current

end Silmaril.SSA.SeaOfNodes.Quads
