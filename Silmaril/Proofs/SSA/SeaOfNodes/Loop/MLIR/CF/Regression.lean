module

import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF

open SeaOfNodes.MLIR (Word sourceInputs)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

private def i8 : Width := ⟨8, by decide⟩
private abbrev byte : Diamond.Ty Width := .value (.data i8)
private abbrev pred : Diamond.Ty Width := .value .predicate
private abbrev entrySigs : List (List (Diamond.Ty Width)) := [[byte], [byte]]
private abbrev headerSigs : List (List (Diamond.Ty Width)) := [[byte], [pred], [byte], [byte]]

-- Initialize the latch to seed + 1, advance by increment while latch < limit,
-- and return latch + seed. The header uses two unequal captured inputs.
private def count (increment : Word i8) : Program [i8, i8] i8 i8 entrySigs headerSigs where
  preheader :=
    .cons (.arithmetic (.constant (1 : Word i8))) .nil
      (.cons (.arithmetic (.binary .addi))
        (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  header :=
    .cons (.arithmetic (.constant increment)) .nil
      (.cons (.ult i8)
        (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil))
        (.cons (.arithmetic (.binary .addi))
          (.cons (.arg (.tail (.tail .head))) (.cons (.output (0 : Fin 2) .head) .nil))
          (.cons (.arithmetic (.binary .addi))
            (.cons (.arg (.tail (.tail .head))) (.cons (.arg .head) .nil)) .nil)))
  phiInputs
    | .entry => .cons (.output (1 : Fin 2) .head) .nil
    | .backedge => .cons (.output (2 : Fin 4) .head) .nil
  predicate := .output (1 : Fin 4) .head
  result := .output (3 : Fin 4) .head

private def input (seed limit : Word i8) : Env [i8, i8] := .cons seed (.cons limit .nil)

private def typed : Cfg TargetOp (Label i8 i8) [i8, i8] [i8] := lower (count 1)

private theorem twoBackedges : typed.run evalOp 5 (input 2 5) = some (.cons (7 : Word i8) .nil) :=
  rfl

private theorem shortBudget : typed.run evalOp 4 (input 2 5) = none := rfl

private theorem immediateExit : typed.run evalOp 3 (input 4 5) = some (.cons (9 : Word i8) .nil) :=
  rfl

private theorem partialReturn :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed typed).denotePart evalOp (input 2 5) =
      Part.some (.returned (.cons (7 : Word i8) .nil)) :=
  (Silmaril.MLIR.CF.SwitchAssert.Cfg.denotePart_eq_some_iff _ _ _ _).mpr
    ⟨5, by rw [Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_run, twoBackedges]; rfl⟩

private theorem nonreturning : (lower (count 0)).Diverges evalOp (input 2 5) := by
  apply (lower_diverges_iff (count 0) (input 2 5)).mpr
  intro domain
  obtain ⟨value, observed⟩ := Part.dom_iff_mem.mp domain
  let old : RVSDG.Tuple (Diamond.Val Word) (Diamond.dataPorts [.data i8]) := .cons (3 : Word i8) .nil
  refine (count 0).not_returns_of_backedge_invariant model (sourceInputs (input 2 5)) value
    (· = old) rfl (fun latch same => same.symm ▸ ⟨old, rfl, rfl⟩)
    (((count 0).returns_iff_mem_denote model (sourceInputs (input 2 5)) value).mpr observed)

private theorem partialDivergence :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower (count 0))).denotePart evalOp (input 2 5) =
      Part.none :=
  (Silmaril.MLIR.CF.SwitchAssert.Cfg.denotePart_eq_none_iff _ _ _).mpr
    ((Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_diverges_iff _ _ _).mpr nonreturning)

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF
