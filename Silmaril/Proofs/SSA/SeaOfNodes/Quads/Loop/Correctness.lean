module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Proofs

open RVSDG (PortType Port Tuple Origin Wires Locals extend)
open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Silmaril.SSA.SeaOfNodes.Loop (Graph appendTuple headerPorts)

universe u v w
variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out test : ValueSort Data}
variable {args : List (Ty Data)} {past : List (List (Ty Data))}

private def withResult (result : Port (dataPorts regs) (.value out)) :
    Code Op regs test → Code Op regs out
  | .ret _ => .ret result
  | .assign dest op operands rest => .assign dest op operands (withResult result rest)

private theorem eval_withResult (code : Code Op regs test) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) (result : Port (dataPorts regs) (.value out)) :
    (withResult result code).eval m entry = (finalBank m code entry).get result := by
  induction code generalizing entry with
  | ret => rfl
  | assign _ _ _ _ ih => exact ih _

private theorem read_get (m : Model.{u, v, w} Op) {ports : List (Ty Data)} {t : Ty Data}
    (current : Wires args past ports) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) (port : Port ports t) :
    (current.read entry locals).get port = Diamond.read m (current.get port) entry locals := by
  induction port with
  | head => cases current; rfl
  | tail _ ih => cases current; exact ih _

private theorem tuple_ext {T : Type u} {F : T → Type w} {ts : List T} (xs ys : Tuple F ts)
    (agree : ∀ {t} (port : Port ts t), xs.get port = ys.get port) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons head tail ih =>
    cases ys with
    | cons other rest =>
      exact (congrArg (fun value => Tuple.cons value tail) (agree .head)).trans
        (congrArg (Tuple.cons other) (ih rest (fun p => agree (.tail p))))

private theorem observe_lowerFrom (code : Code Op regs test) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) (result : Port (dataPorts regs) (.value out)) :
    Diamond.read m ((compile code current).outgoing.get result) entry
      ((compile code current).flow.eval m entry locals) =
      (((withResult result code).lowerFrom current).eval m.toRVSDG entry locals).get .head := by
  induction code generalizing past with
  | ret => rfl
  | assign dest _ _ _ ih => exact ih _ (rebind current dest)

private theorem port_value {t : Ty Data} (port : Port (dataPorts regs) t) :
    ∃ sort, t = PortType.value sort := by
  induction regs with
  | nil => cases port
  | cons sort _ ih =>
    cases port with
    | head => exact ⟨sort, rfl⟩
    | tail p => exact ih p

theorem compile_agrees (code : Code Op regs test) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (compile code current).outgoing.read entry ((compile code current).flow.eval m entry locals) =
      finalBank m code (current.read entry locals) := by
  apply tuple_ext
  intro t port
  obtain ⟨sort, rfl⟩ := port_value port
  have selected := congrArg (fun tuple : Tuple (Val m.value) [.value sort] => tuple.get .head)
    ((withResult port code).lowerFrom_eval m entry locals current)
  exact (read_get m _ entry _ port).trans
    ((observe_lowerFrom code m entry locals current port).trans
      (selected.trans (eval_withResult code m (current.read entry locals) port)))

private theorem read_tabulate (m : Model.{u, v, w} Op) (ports : List (Ty Data))
    (wires : ∀ {t}, Port ports t → Origin args past t)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    Wires.read (tabulate ports wires) entry locals =
      tabulate ports (fun p => Diamond.read m (wires p) entry locals) := by
  induction ports with
  | nil => rfl
  | cons _ _ ih =>
    exact congrArg (Tuple.cons (Diamond.read m (wires .head) entry locals)) (ih (fun p => wires (.tail p)))

private theorem tabulate_get {T : Type u} {F : T → Type w} {ts : List T} (tuple : Tuple F ts) :
    tabulate ts (fun p => tuple.get p) = tuple := by
  induction tuple with
  | nil => rfl
  | cons head _ ih => exact congrArg (Tuple.cons head) ih

private theorem carry_get {T : Type u} {F : T → Type w} {xs ys : List T} {t : T}
    (input : Tuple F xs) (old : Tuple F ys) (port : Port ys t) :
    (appendTuple old input).get (carryPort port xs) = old.get port := by
  induction input with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem header_read (m : Model.{u, v, w} Op)
    (input old : Tuple (Val m.value) (dataPorts regs)) :
    (headerVersions regs).read (appendTuple old input) PUnit.unit = old :=
  (read_tabulate (past := []) m _ (fun port => .arg (carryPort port (dataPorts regs)))
    (appendTuple old input) PUnit.unit).trans
      ((congrArg (tabulate (dataPorts regs)) (funext fun _ => funext fun p => carry_get input old p)).trans
        (tabulate_get old))

theorem lower_initial (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (input : Tuple (Val m.value) (dataPorts regs)) :
    p.lower.initial m input = input :=
  (read_tabulate (past := []) m _ (fun port => .arg port) input PUnit.unit).trans (tabulate_get input)

theorem lower_step (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (input old : Tuple (Val m.value) (dataPorts regs)) :
    p.lower.step m input old = p.step m old := by
  let entry := appendTuple old input
  let transfer := compile p.activation (headerVersions regs)
  let locals := transfer.flow.eval m entry PUnit.unit
  let updated := finalBank m p.activation old
  have bank : transfer.outgoing.read entry locals = updated :=
    (compile_agrees p.activation m entry (past := []) PUnit.unit (headerVersions regs)).trans
      (congrArg (finalBank m p.activation) (header_read m input old))
  have readPort {t : Ty Data} (port : Port (dataPorts regs) t) :
      Diamond.read m (transfer.outgoing.get port) entry locals = updated.get port :=
    (read_get m transfer.outgoing entry locals port).symm.trans (congrArg (fun xs => xs.get port) bank)
  change (if (Diamond.read m (transfer.outgoing.get (returnPort p.activation)) entry locals).down then
    Sum.inr (transfer.outgoing.read entry locals)
    else Sum.inl (Diamond.read m (transfer.outgoing.get p.result) entry locals)) =
    (if (updated.get (returnPort p.activation)).down then Sum.inr updated else Sum.inl (updated.get p.result))
  rw [readPort, readPort, bank]

theorem lower_returnsAfter_iff (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (input old : Tuple (Val m.value) (dataPorts regs)) (count : Nat) (result : sortValue m.value out) :
    p.lower.ReturnsAfter m input count old result ↔ p.ReturnsAfter m count old result := by
  constructor
  · intro run
    induction run with
    | @exit old _ taken => exact .exit ((lower_step p m input old).symm.trans taken)
    | @backedge _ old _ _ taken _ ih => exact .backedge ((lower_step p m input old).symm.trans taken) ih
  · intro run
    induction run with
    | @exit old _ taken => exact .exit ((lower_step p m input old).trans taken)
    | @backedge _ old _ _ taken _ ih => exact .backedge ((lower_step p m input old).trans taken) ih

theorem lower_returns_iff (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (input : Tuple (Val m.value) (dataPorts regs)) (result : sortValue m.value out) :
    p.lower.Returns m input result ↔ p.Returns m input result := by
  change (∃ count, p.lower.ReturnsAfter m input count (p.lower.initial m input) result) ↔ _
  rw [lower_initial]
  exact exists_congr fun count => lower_returnsAfter_iff p m input input count result

private theorem lower_evalFrom (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (input : Tuple (Val m.value) (dataPorts regs)) (budget : Nat)
    (old : Tuple (Val m.value) (dataPorts regs)) :
    p.lower.evalFrom m input budget old = p.evalBackedges m budget old := by
  induction budget generalizing old with
  | zero => simp only [Graph.evalFrom, Program.evalBackedges, lower_step] <;> rfl
  | succ _ ih =>
    simp only [Graph.evalFrom, Program.evalBackedges, lower_step]
    cases p.step m old with
    | inl => rfl
    | inr next => exact ih next

theorem lower_evalBackedges (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (budget : Nat) (input : Tuple (Val m.value) (dataPorts regs)) :
    p.lower.evalBackedges m budget input = p.evalBackedges m budget input :=
  (lower_evalFrom p m input budget (p.lower.initial m input)).trans
    (congrArg (p.evalBackedges m budget) (lower_initial p m input))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Proofs
