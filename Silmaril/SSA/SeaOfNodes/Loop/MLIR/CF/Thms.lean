module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Correctness
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

/-! Typed MLIR CFG execution preserves and reflects all pure single-loop returns. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF

open SeaOfNodes.MLIR (Word sourceInputs)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable (g : Program Γ carried result entrySigs headerSigs) (input : Env Γ)

/-- The entry, final header test and exit account for the three extra blocks. -/
theorem lower_run (budget : Nat) :
    (lower g).run evalOp (budget + 3) input =
      (g.evalBackedges model budget (sourceInputs input)).map (fun value => Env.cons value .nil) :=
  Proofs.run_budget g input budget

/-- Each native finite return agrees with some finite execution of the typed CFG,
and every such target return is a native finite return. -/
theorem lower_returns_iff (value : Word result) :
    g.Returns model (sourceInputs input) value ↔
      ∃ fuel, (lower g).run evalOp fuel input = some (.cons value .nil) :=
  Proofs.returns_iff g input value

/-- The existing partial CFG denotation returns the source word as a singleton
result vector. Its domain is exactly the native loop's domain. -/
theorem lower_denotePart :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) :=
  Proofs.denotePart_eq g input

theorem lower_diverges_iff :
    (lower g).Diverges evalOp input ↔ ¬ (g.denote model (sourceInputs input)).Dom := by
  rw [← Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_diverges_iff,
    ← Silmaril.MLIR.CF.SwitchAssert.Cfg.denotePart_eq_none_iff, lower_denotePart, Part.eq_none_iff']
  rfl

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF
