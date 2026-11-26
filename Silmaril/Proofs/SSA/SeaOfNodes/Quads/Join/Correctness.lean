module

public import Silmaril.SSA.SeaOfNodes.Quads.Join.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Join.Proofs

open RVSDG (PortType Port Tuple Origin Wires Locals)
open Diamond (Ty ValueSort Signature Model Val dataPorts sortValue Merge Projection Slot)

universe u v w
variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {args outs : List (Ty Data)} {past : List (List (Ty Data))}

theorem predecessor_selected (merge : Merge) (condition : Bool) :
    merge.predecessor (selected merge condition) = Projection.ofBool condition := by
  rcases merge with ⟨first⟩
  cases first <;> cases condition <;> rfl

private theorem slotAt_index (edge : Slot) : slotAt (slotIndex edge) = edge := by
  cases edge <;> rfl

private theorem exit_read (exit : Exit regs outs) (m : Model.{u, v, w} Op)
    (current : Wires args past (dataPorts regs)) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) :
    Wires.read (exit.select current) entry locals = exit.select (current.read entry locals) := by
  cases exit with
  | jump => rfl
  | ret result =>
    exact congrArg (fun value => Tuple.cons (F := Val m.value) value .nil)
      (read_get m current entry locals result).symm

private theorem lowerFrom_eval (block : Block Op regs) (exit : Exit regs outs)
    (m : Model.{u, v, w} Op) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) (current : Wires args past (dataPorts regs)) :
    (block.lowerFrom current exit).eval (model m) entry locals =
      exit.select (block.eval m (current.read entry locals)) := by
  induction block generalizing past with
  | nil => exact exit_read exit m current entry locals
  | cons quad rest ih =>
    let produced : Tuple (Val m.value) [.value quad.result] :=
      .cons (m.run quad.op ((quad.inputWires current).read entry locals)) .nil
    change (Block.lowerFrom rest (rebind current quad.dest) exit).eval (model m)
      entry (locals.snoc produced) = _
    exact (ih (locals.snoc produced) (rebind current quad.dest)).trans
      (congrArg (fun bank => exit.select (Block.eval rest m bank))
        (quad.step_read m entry locals current))

private theorem prepend_results {head : List (Ty Data)} {sigs : List (List (Ty Data))}
    (node : RVSDG.Node (Opcode Op) args past head)
    (children : RVSDG.Children (RVSDG.Graph (Opcode Op)) node)
    (rest : RVSDG.Graph (Opcode Op) args (past ++ [head]) sigs outs) :
    (rest.prepend node children).results = rest.results := by
  cases rest
  rfl

private theorem lowerFrom_results (block : Block Op regs) (exit : Exit regs outs)
    (current : Wires args past (dataPorts regs)) :
    (block.lowerFrom current exit).toGraph.results = exit.select (block.versions current) := by
  induction block generalizing past with
  | nil => rfl
  | cons quad rest ih =>
    simp only [Block.lowerFrom, RVSDG.Term.toGraph, Block.versions]
    exact (prepend_results _ _ _).trans (ih (rebind current quad.dest))

theorem arm_results (p : Program Op regs out) (i : Fin 2) :
    (p.arm i).toGraph.results = p.incoming (slotAt i) :=
  lowerFrom_results (p.predecessor (slotAt i)) .jump (initial regs)

private theorem arm_run (p : Program Op regs out) (i : Fin 2) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    (p.arm i).run (model m) entry = (p.predecessor (slotAt i)).eval m entry := by
  exact (lowerFrom_eval (p.predecessor (slotAt i)) .jump m entry (past := []) PUnit.unit
    (initial regs)).trans (congrArg (Block.eval (p.predecessor (slotAt i)) m) (read_initial m entry))

theorem arm_graph_run (p : Program Op regs out) (i : Fin 2) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    (p.arm i).toGraph.run (model m) entry = (p.predecessor (slotAt i)).eval m entry :=
  (RVSDG.Term.run_toGraph _ _ _).trans (arm_run p i m entry)

private theorem read_args (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) (locals : Locals (Val m.value) past) :
    Wires.read (tabulate _ (fun p => .arg p)) entry locals = entry :=
  (read_tabulate m _ (fun p => .arg p) entry locals).trans (tabulate_get_eq entry)

private theorem read_join (m : Model.{u, v, w} Op)
    (entry bank : Tuple (Val m.value) (dataPorts regs))
    (tag : Tuple (Val m.value) [.control 2]) :
    (Program.joinWires regs).read entry ((tag, (bank, PUnit.unit)) :
      Locals (Val m.value) [[.control 2], dataPorts regs]) = bank :=
  (read_tabulate (past := [[.control 2], dataPorts regs]) m _ (fun p => .output (1 : Fin 2) p) entry _).trans (tabulate_get_eq bank)

private theorem lowerTerm_run (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    p.lowerTerm.run (model m) entry = .cons (p.eval m entry) .nil := by
  let choice := slotIndex (p.selectedSlot m entry)
  let tag : Tuple (Val m.value) [.control 2] := .cons ⟨choice⟩ .nil
  let controlLocals : Locals (Val m.value) [[.control 2]] := (tag, PUnit.unit)
  let capture := Wires.read (tabulate _ (fun p => .arg p)) entry controlLocals
  let result := (p.arm choice).run (model m) capture
  change (p.join.lowerFrom (Program.joinWires regs) (.ret p.result)).eval (model m)
    entry (controlLocals.snoc result) = _
  have result_eq : result = (p.predecessor (p.selectedSlot m entry)).eval m entry := by
    calc
      _ = (p.arm choice).run (model m) entry :=
        congrArg (fun bank => (p.arm choice).run (model m) bank) (read_args m entry controlLocals)
      _ = _ := (arm_run p choice m entry).trans
        (congrArg (fun edge => (p.predecessor edge).eval m entry)
          (slotAt_index (p.selectedSlot m entry)))
  calc
    _ = (Exit.ret p.result).select (p.join.eval m
        ((Program.joinWires regs).read entry (controlLocals.snoc result))) :=
      lowerFrom_eval p.join (.ret p.result) m entry (controlLocals.snoc result) (Program.joinWires regs)
    _ = _ := congrArg (fun bank => (Exit.ret p.result).select (p.join.eval m bank))
      ((read_join m entry result tag).trans result_eq)

theorem lower_run (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    p.lower.run (model m) entry = .cons (p.eval m entry) .nil :=
  (RVSDG.Term.run_toGraph _ _ _).trans (lowerTerm_run p m entry)

end Silmaril.SSA.SeaOfNodes.Quads.Join.Proofs
