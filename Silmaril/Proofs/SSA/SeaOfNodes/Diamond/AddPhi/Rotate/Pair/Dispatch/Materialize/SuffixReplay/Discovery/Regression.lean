module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Defs
import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Regression

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (InputWord Program residualAdd)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay (blockOf)
open AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery (normalize)
open Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay (Block)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

open Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery (unused? step?)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort]]

private def source : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 3) .nil (.cons (.literal 0) .nil .nil)
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil) }
    | .second => {
        sigs := [[wordPort]]
        dataflow := .cons .sub (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)) .nil
        outputs := .cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil) }

private def x : InputWord inputs := .tail (.tail .head)

private def observe {joined : List (ValueSort Unit)} (p : Program inputs sigs joined) (guard : Bool) :
    BitVec 64 :=
  let entry : Tuple (Val model.value) (dataPorts inputs) :=
    .cons ⟨guard⟩ (.cons (41 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil))
  p.denote entry

theorem redirection_exposes_literal_deletion_in_the_actual_suffix :
    (rewrite source x .left).map (fun result => match result with
      | .materialized .right _ p =>
        let before := (Cleanup.UnusedZero.leadingZero? p.suffix).map fun zero =>
          (unused? (blockOf p) zero).isNone
        let run := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize (blockOf p)
        let target := normalize p
        some (before, run.rules, target.suffix, target.diamond.merge,
          (target.diamond.arms .first).outputs.addresses, (target.diamond.arms .second).outputs.addresses,
          observe target false, observe target true)
      | _ => none) =
      .ok (some (some true, [.rightZero, .deleteUnused], residualAdd, ⟨.onFalse⟩,
        [.output 0 0], [.output 2 0],
        observe (AddPhi.Rotate.Pair.original source x) false, observe (AddPhi.Rotate.Pair.original source x) true)) ∧
    (observe (AddPhi.Rotate.Pair.original source x) false, observe (AddPhi.Rotate.Pair.original source x) true) =
      (2, 41) := ⟨rfl, rfl⟩

private def packetExample (keepZero : Bool) : Block [word] [wordPort] where
  sigs := [[wordPort], [wordPort]]
  flow := .cons (.literal 0) .nil
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  packet := .cons (.output (1 : Fin 2) .head)
    (.cons (if keepZero then .output (0 : Fin 2) .head else .arg .head) .nil)

private def packetSummary (keepZero : Bool) :=
  let final := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize (packetExample keepZero)
  (final.rules, final.state.block.sigs.length, final.state.block.packet.addresses)

theorem second_packet_field_keeps_the_literal_live_after_redirection :
    packetSummary true = ([.rightZero], 1, [.arg 0, .output 0 0]) ∧
    packetSummary false = ([.rightZero, .deleteUnused], 0, [.arg 0, .arg 0]) := ⟨rfl, rfl⟩

private def literalPriority : Block [] [] where
  sigs := [[wordPort], [wordPort], [wordPort]]
  flow := .cons (.literal 5) .nil (.cons (.literal 0) .nil
    (.cons .add (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)) .nil))
  packet := .cons (.output (2 : Fin 3) .head) .nil

theorem higher_priority_literal_fold_blocks_right_zero :
    step? literalPriority = none := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Regression
