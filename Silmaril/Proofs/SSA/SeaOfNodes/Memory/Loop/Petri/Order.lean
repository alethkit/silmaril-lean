module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs
import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Firing.Proofs

open RVSDG (Dialect Origin Port Tuple Wires)
open RVSDG.OrderedRuntime.Structured (Threaded Ty get_runtime nextRuntime runtime runtimePort)
open RVSDG.Petri (Tokens Vertex absent collect colour read)
open RVSDG.NestedTheta.Petri (Fire Marking pending)

universe u

variable {args : List ValueSort}

private theorem captured_heap {entry : List (Ty ValueSort)} {past : List (List (Ty ValueSort))}
    (live : Origin entry past runtime) (wire : ∀ {t}, Port (carrier args) t → Origin entry past t) :
    (inputsWithHeap live args wire).get (runtimePort (dataPorts args)) = live := by
  induction args with
  | nil => rfl
  | cons _ _ ih => exact ih (fun p => wire (.tail p))

private theorem compiled_chain (stop : Port args .word) :
    {locals : List (List ValueSort)} → {version : Nat} → {past : List (List (Ty ValueSort))} →
    (body : Memory.Body args locals version) → (routing : Routing args locals past) →
    (live : Origin (carrier args) past runtime) →
    HeapChain ThetaOpcode (carrier args) (Threaded (tagged args)) live
      (testAfter stop (RVSDG.Institution.mapTerm liftMemory (body.lowerFrom routing live).term))
  | _, _, _, .ret _ value, routing, live =>
    .bind (ins := tested args) _ (.cons (routing value) (inputsWithHeap live args (fun p => .arg p)))
      (captured_heap live (fun p => .arg p)) (.ret _)
  | _, _, _, .load _ _ rest, routing, live =>
    .bind _ _ (get_runtime live _)
      (compiled_chain stop rest routing.afterLoad (nextRuntime _ wordPorts))
  | _, _, _, .store _ _ _ rest, routing, live =>
    .bind _ _ (get_runtime live _)
      (compiled_chain stop rest routing.afterStore (nextRuntime _ []))

theorem theta_chain (graph : Graph args) :
    HeapChain ThetaOpcode (carrier args) (Threaded (tagged args))
      (.arg (runtimePort (dataPorts args))) graph.thetaBody :=
  compiled_chain graph.stop graph.body (Routing.entry args) (.arg (runtimePort (dataPorts args)))

variable {Op : Dialect ValueSort PUnit} {model : RVSDG.Model Op}
variable {entry outs : List (Ty ValueSort)} {past sigs : List (List (Ty ValueSort))}
variable {t : RVSDG.Term Op entry past sigs outs} {live : Origin entry past runtime}

private theorem get_collected {F : Ty ValueSort → Type u} {ports : List (Ty ValueSort)} {s : Ty ValueSort}
    (p : Port ports s) {xs : Tuple (fun a => Option (F a)) ports} {out : Tuple F ports}
    (h : collect xs = some out) : xs.get p = some (out.get p) := by
  induction p with
  | head =>
    cases xs with
    | cons value tail =>
      simp only [collect] at h
      split at h
      · cases h
        rfl
      · cases h
  | tail p ih =>
    cases xs with
    | cons value tail =>
      simp only [collect] at h
      split at h
      · cases h
        exact ih (by assumption)
      · cases h

private theorem get_map {F : Ty ValueSort → Type} {G : Ty ValueSort → Type u}
    {ports : List (Ty ValueSort)} {s : Ty ValueSort}
    (p : Port ports s) (xs : Tuple F ports) (f : ∀ a, F a → G a) :
    (xs.map f).get p = f s (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs with | cons _ tail => exact ih tail

private theorem read_colour {ins : List (Ty ValueSort)} {s : Ty ValueSort}
    (p : Port ins s) (wires : Wires entry past ins) (input : Tuple model.Val entry)
    (tokens : Tokens model.Val past) {out : Tuple model.Val ins}
    (ready : read wires input tokens = some out) :
    colour input tokens (wires.get p) = some (out.get p) :=
  (get_map p wires (fun _ => colour input tokens)).symm.trans (get_collected p ready)

private theorem absent_get {F : Ty ValueSort → Type u} {ports : List (Ty ValueSort)} {s : Ty ValueSort}
    (p : Port ports s) : (absent (F := F) ports).get p = none := by
  induction p with
  | head => rfl
  | tail _ ih => exact ih

private theorem missing_next {out : List (Ty ValueSort)} (input : Tuple model.Val entry)
    (tokens : Tokens model.Val past) :
    colour input (tokens.snoc (absent (Threaded out))) (nextRuntime past out) = none := by
  induction past with
  | nil => exact absent_get (runtimePort out)
  | cons _ _ ih => exact ih tokens.2

private theorem pending_blocked (chain : HeapChain Op entry outs live t)
    (input : Tuple model.Val entry) (tokens : Tokens model.Val past)
    (missing : colour input tokens live = none) {mark : Marking model (.ofBase t)}
    (fired : Fire model (.ofBase t) input tokens (pending model (.ofBase t)) mark) : False := by
  induction chain with
  | ret => cases fired
  | bind op wires edge tail ih =>
    cases fired with
    | primitive ready _ =>
      have marked := read_colour (runtimePort _) wires input tokens ready
      rw [edge, missing] at marked
      cases marked
    | enter _ guard => cases guard
    | later step =>
      exact ih _ (missing_next input tokens) step

theorem prefix_initial (model : RVSDG.Model Op)
    (term : RVSDG.NestedTheta.Term Op entry past sigs outs) :
    DonePrefix model term (pending model term) 0 := by
  cases term with
  | ret => rfl
  | bind => exact ⟨rfl, rfl⟩

theorem prefix_step (chain : HeapChain Op entry outs live t)
    (input : Tuple model.Val entry) (tokens : Tokens model.Val past)
    {before after : Marking model (.ofBase t)} {count : Nat}
    (ordered : DonePrefix model (.ofBase t) before count)
    (fired : Fire model (.ofBase t) input tokens before after) :
    DonePrefix model (.ofBase t) after (count + 1) := by
  induction chain generalizing count with
  | ret => cases fired
  | bind op wires edge chain ih =>
    obtain ⟨vertex, tail⟩ := before
    cases vertex with
    | waiting => exact False.elim ordered
    | pending =>
      obtain ⟨rfl, rfl⟩ := ordered
      cases fired with
      | primitive _ _ => exact ⟨0, rfl, prefix_initial _ _⟩
      | enter _ guard => cases guard
      | later step => exact False.elim (pending_blocked chain input _ (missing_next input tokens) step)
    | done previous =>
      obtain ⟨count, rfl, ordered⟩ := ordered
      cases fired with
      | later step => exact ⟨count + 1, rfl, ih _ ordered step⟩

theorem completed_prefix_length (term : RVSDG.NestedTheta.Term Op entry past sigs outs)
    (input : Tuple model.Val entry) (tokens : Tokens model.Val past)
    {mark : Marking model term} {count : Nat} {output : Tuple model.Val outs}
    (ordered : DonePrefix model term mark count)
    (completed : RVSDG.NestedTheta.Petri.finished model term input tokens mark = some output) :
    count = sigs.length := by
  induction term generalizing count with
  | ret => exact ordered
  | bind node children rest _ ih =>
    obtain ⟨vertex, tail⟩ := mark
    cases vertex with
    | pending | waiting => cases completed
    | done value =>
      obtain ⟨count, rfl, order⟩ := ordered
      exact congrArg Nat.succ (ih _ _ order completed)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Firing.Proofs
