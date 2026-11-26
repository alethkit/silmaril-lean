module

public import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Finite.Correctness

/-! # Exact occurrence and sequential execution agreement for finite quad joins -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Join.Finite

open RVSDG (Locals Tuple Wires)
open Diamond (Ty ValueSort Signature Model Val dataPorts)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)}

/-- The new bank at the end of a producer prefix reads back in port order. -/
theorem lastBank_read {args head : List (Ty Data)} {past : List (List (Ty Data))}
    (m : Model.{u, v, w} Op) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) (bank : Tuple (Val m.value) head) :
    (lastBank past head).read entry (locals.snoc bank) = bank :=
  Proofs.lastBank_read m entry locals bank

/-- Each numbered child returns the column obtained from its own reaching versions. -/
theorem Table.arm_results (table : Table Op regs) (edge : Fin table.length) :
    (Table.arm table edge).toGraph.results = Table.incoming table edge :=
  Proofs.arm_results table edge

/-- Selecting an occurrence recovers the whole bank computed by that predecessor. -/
theorem Table.arm_run (table : Table Op regs) (edge : Fin table.length) (m : Model.{u, v, w} Op)
    (bank : Tuple (Val m.value) (dataPorts regs)) :
    (Table.arm table edge).toGraph.run (model m) bank = Block.eval (table.get edge) m bank :=
  Proofs.arm_graph_run table edge m bank

/-- The target occurrence selected by the predicate tests has the source stage's result. -/
theorem Stage.selected_run (stage : Stage Op regs) (m : Model.{u, v, w} Op)
    (bank : Tuple (Val m.value) (dataPorts regs)) :
    (Table.arm stage.table (stage.choice.eval bank)).toGraph.run (model m) bank =
      stage.eval m bank :=
  Table.arm_run stage.table (stage.choice.eval bank) m bank

/-- The compiler composes under any typed map into an existing prefix. -/
theorem Plan.lowerFrom_eval {args : List (Ty Data)} {past : List (List (Ty Data))}
    (plan : Plan Op regs) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (Plan.lowerFrom plan current).eval (model m) entry locals =
      Plan.eval plan m (current.read entry locals) :=
  Proofs.lowerFrom_eval plan m entry locals current

/-- Numbered evaluation agrees with ordered quad execution on the entire returned bank. -/
theorem Plan.lower_run (plan : Plan Op regs) (m : Model.{u, v, w} Op)
    (bank : Tuple (Val m.value) (dataPorts regs)) :
    (Plan.lower plan).run (model m) bank = Plan.eval plan m bank :=
  Proofs.lower_run plan m bank

/-- An appended plan has the same observation as feeding the first graph's bank to the second. -/
theorem Plan.lower_append_run (first rest : Plan Op regs) (m : Model.{u, v, w} Op)
    (bank : Tuple (Val m.value) (dataPorts regs)) :
    (Plan.lower (first ++ rest)).run (model m) bank =
      (Plan.lower rest).run (model m) ((Plan.lower first).run (model m) bank) :=
  Proofs.lower_append_run first rest m bank

end Silmaril.SSA.SeaOfNodes.Quads.Join.Finite
