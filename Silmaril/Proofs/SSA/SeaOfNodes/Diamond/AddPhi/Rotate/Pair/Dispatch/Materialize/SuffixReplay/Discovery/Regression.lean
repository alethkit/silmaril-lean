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
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (Opcode model word wordPort)
open Silmaril.SSA.SeaOfNodes.GVN (newest weaken)
open Silmaril.SSA.RVSDG (Origin Tuple Wires extend)

open Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery (unused? step? addCount)

private abbrev inputs : List (ValueSort Unit) := [.predicate, word, word]
private abbrev sigs := [[wordPort], [wordPort]]

private def sourceWith (right : BitVec 64) : AddPhi.Pair.Source inputs sigs where
  shared := .cons (.literal 3) .nil (.cons (.literal right) .nil .nil)
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

private def source := sourceWith 0

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

theorem higher_priority_literal_fold_keeps_the_table_size :
    (step? literalPriority).map (fun edit =>
      (edit.rule, edit.state.block.sigs.length, addCount edit.state.block)) =
        some (.literal, 3, 0) := rfl

private abbrev args := dataPorts [word, word]
private abbrev row := [wordPort]

/-- Test-only tail on the actual emitted table: add the wrapping sum to the
old result and make the sum itself the other outgoing value. -/
private def appendWrappingAdd : {past sigs : List (List (Ty Unit))} →
    Dataflow Opcode args past sigs → Origin args (extend past sigs) wordPort →
    Σ newSigs, Dataflow Opcode args past newSigs ×
      Wires args (extend past newSigs) [wordPort, wordPort]
  | past, _, .nil, old =>
    let maxWire : Origin args (past ++ [row]) wordPort := newest .head
    let oneWire : Origin args ((past ++ [row]) ++ [row]) wordPort := newest .head
    let sumWire : Origin args (((past ++ [row]) ++ [row]) ++ [row]) wordPort := newest .head
    let old := weaken row (weaken row (weaken row old))
    ⟨[row, row, row, row],
      .cons (.literal 0xffffffffffffffff) .nil
        (.cons (.literal 1) .nil
          (.cons .add (.cons (weaken row maxWire) (.cons oneWire .nil))
            (.cons .add (.cons old (.cons sumWire .nil)) .nil))),
      .cons (newest .head) (.cons (weaken row sumWire) .nil)⟩
  | _, _, .cons opcode operands rest, old =>
    let ⟨_, flow, packet⟩ := appendWrappingAdd rest old
    ⟨_, .cons opcode operands flow, packet⟩

private def withWrappingAdd (p : Program inputs sigs [word]) : Block [word, word] [wordPort] :=
  let ⟨sigs, flow, packet⟩ := appendWrappingAdd p.suffix.dataflow p.suffix.result
  ⟨sigs, flow, packet⟩

private def packetAt (p : Program inputs sigs [word]) (block : Block [word, word] [wordPort]) (guard : Bool) :
    BitVec 64 × BitVec 64 :=
  let entry : Tuple (Val model.value) (dataPorts inputs) :=
    .cons ⟨guard⟩ (.cons (41 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil))
  let suffixEntry : Tuple (Val model.value) args :=
    .cons (entry.get p.residual) (p.diamond.denote model entry)
  let values := block.packet.read suffixEntry (block.flow.eval model suffixEntry PUnit.unit)
  (values.get .head, values.get (.tail .head))

theorem wrapping_fold_exposes_right_zero_and_keeps_the_second_packet_value :
    (rewrite (sourceWith 7) x .left).map (fun result => match result with
      | .materialized .right _ p =>
        let ext := withWrappingAdd p
        let first := (step? ext).map fun edit => (edit.rule, edit.state.block.sigs.length, addCount edit.state.block)
        let final := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize ext
        some (first, final.rules, final.state.block.packet.addresses,
          packetAt p ext false, packetAt p final.state.block false,
          packetAt p ext true, packetAt p final.state.block true)
      | _ => none) =
      .ok (some (some (.literal, 7, 3), [.literal, .rightZero, .deleteUnused, .deleteUnused],
        [.output 2 0, .output 3 0], (9, 0), (9, 0), (48, 0), (48, 0))) := rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Regression
