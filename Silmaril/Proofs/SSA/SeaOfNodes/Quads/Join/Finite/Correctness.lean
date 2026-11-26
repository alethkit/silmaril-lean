module

public import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Proofs

open RVSDG (PortType Port Tuple Wires Locals)
open Diamond (Ty ValueSort Signature Model Val dataPorts)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)}
variable {args head : List (Ty Data)} {past : List (List (Ty Data))}

theorem arm_results (table : Table Op regs) (edge : Fin table.length) :
    (Table.arm table edge).toGraph.results = Table.incoming table edge :=
  Block.lowerFrom_results (table.get edge) .jump (initial regs)

private theorem arm_run (table : Table Op regs) (edge : Fin table.length) (m : Model.{u, v, w} Op)
    (bank : Tuple (Val m.value) (dataPorts regs)) :
    (Table.arm table edge).run (model m) bank = Block.eval (table.get edge) m bank :=
  (Block.lowerFrom_eval (table.get edge) .jump m bank (past := []) PUnit.unit (initial regs)).trans
    (congrArg (Block.eval (table.get edge) m) (read_initial m bank))

theorem arm_graph_run (table : Table Op regs) (edge : Fin table.length) (m : Model.{u, v, w} Op)
    (bank : Tuple (Val m.value) (dataPorts regs)) :
    (Table.arm table edge).toGraph.run (model m) bank = Block.eval (table.get edge) m bank :=
  (RVSDG.Term.run_toGraph _ _ _).trans (arm_run table edge m bank)

private theorem last_get {F : Ty Data → Type w} {t : Ty Data} (port : Port head t)
    (locals : Locals F past) (bank : Tuple F head) :
    ((locals.snoc bank).get (Diamond.lastIndex head past)).get (Diamond.lastPort port past) =
      bank.get port := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

private theorem lastBank_read (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (bank : Tuple (Val m.value) head) :
    (lastBank past head).read entry (locals.snoc bank) = bank := by
  let atPort := fun {t : Ty Data} (port : Port head t) =>
    RVSDG.Origin.output (args := args) (Diamond.lastIndex head past) (Diamond.lastPort port past)
  calc
    _ = tabulate head (fun p => Diamond.read m (atPort p) entry (locals.snoc bank)) :=
      read_tabulate m head atPort entry (locals.snoc bank)
    _ = tabulate head (fun p => bank.get p) :=
      congrArg (tabulate head) (funext fun _ => funext fun p => last_get p locals bank)
    _ = _ := tabulate_get_eq bank

theorem lowerFrom_eval (plan : Plan Op regs) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (Plan.lowerFrom plan current).eval (model m) entry locals =
      Plan.eval plan m (current.read entry locals) := by
  induction plan generalizing past with
  | nil => rfl
  | cons stage rest ih =>
    let bank := current.read entry locals
    let routed : Tuple (Val m.value) stage.routePorts := .cons ⟨stage.choice.eval bank⟩ bank
    let afterRoute := locals.snoc routed
    let runGamma : Tuple (Val m.value) stage.routePorts → Tuple (Val m.value) (dataPorts regs)
      | .cons choice capture => (Table.arm stage.table choice.down).run (model m) capture
    let returned := runGamma ((lastBank past stage.routePorts).read entry afterRoute)
    let next := lastBank (args := args) (past ++ [stage.routePorts]) (dataPorts regs)
    change (Plan.lowerFrom rest next).eval (model m) entry (afterRoute.snoc returned) = _
    have selected : returned = stage.eval m bank :=
      (congrArg runGamma (lastBank_read m entry locals routed)).trans
        (arm_run stage.table (stage.choice.eval bank) m bank)
    exact (ih (afterRoute.snoc returned) next).trans
      (congrArg (Plan.eval rest m) ((lastBank_read m entry afterRoute returned).trans selected))

theorem lower_run (plan : Plan Op regs) (m : Model.{u, v, w} Op)
    (bank : Tuple (Val m.value) (dataPorts regs)) :
    (Plan.lower plan).run (model m) bank = Plan.eval plan m bank := by
  exact (RVSDG.Term.run_toGraph _ _ _).trans
    ((lowerFrom_eval plan m bank (past := []) PUnit.unit (initial regs)).trans
      (congrArg (Plan.eval plan m) (read_initial m bank)))

theorem lower_append_run (first rest : Plan Op regs) (m : Model.{u, v, w} Op)
    (bank : Tuple (Val m.value) (dataPorts regs)) :
    (Plan.lower (first ++ rest)).run (model m) bank =
      (Plan.lower rest).run (model m) ((Plan.lower first).run (model m) bank) := by
  calc
    _ = Plan.eval (first ++ rest) m bank := lower_run _ m bank
    _ = Plan.eval rest m (Plan.eval first m bank) := List.foldl_append ..
    _ = Plan.eval rest m ((Plan.lower first).run (model m) bank) :=
      congrArg (Plan.eval rest m) (lower_run first m bank).symm
    _ = _ := (lower_run rest m _).symm

end Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Proofs
