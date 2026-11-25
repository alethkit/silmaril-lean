module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Tests

private abbrev T := Ty Unit Unit
private abbrev word : T := .value (.data ())
private abbrev state : T := .state ()
private abbrev tag : T := .control 2
private abbrev results : Ports T := [word, state]
private abbrev fn : Function Unit Unit := ⟨[tag, word, state], results⟩
private abbrev callable : T := fn.port
private abbrev bodyArgs : Ports T := callable :: fn.args
private abbrev bumpResult : Ports T := [tag, state]

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | bump : Op [tag, state] bumpResult
  | copy : Op [word] [word]

private def machine : Machine Op where
  Data _ := Nat
  State _ := Nat
  primitive
    | .bump, .cons (.control mode) (.cons (.state n) .nil) =>
      .cons (.control (if mode = 1 ∨ n < 2 then 1 else 0)) (.cons (.state (n + 1)) .nil)
    | .copy, input => input

private def copyNode {past : List (Ports T)} : NestedTheta.Node (Instruction Op) bodyArgs past [word] :=
  ⟨[word], .base (.simple (.primitive .copy)), .cons (.arg (.tail (.tail .head))) .nil, fun i => i.elim0⟩

private def callNode : NestedTheta.Node (Instruction Op) bodyArgs [[word]] results :=
  ⟨bodyArgs, .base (.simple (.apply fn)),
    .cons (.arg .head) (.cons (.arg (.tail .head))
      (.cons (.output 0 .head) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))),
    fun i => i.elim0⟩

private def recurse : NestedTheta.Term (Instruction Op) bodyArgs [] [[word], results] results :=
  .bind copyNode (fun i => i.elim0) <|
    .bind callNode (fun i => i.elim0) <| .ret (forwarding bodyArgs [[word]] results)

private def stop : NestedTheta.Term (Instruction Op) bodyArgs [] [] results :=
  .ret (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))

private def bumpNode : NestedTheta.Node (Instruction Op) bodyArgs [] bumpResult :=
  ⟨bumpResult, .base (.simple (.primitive .bump)),
    .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail (.tail .head)))) .nil), fun i => i.elim0⟩

private def select : NestedTheta.Node (Instruction Op) bodyArgs [bumpResult] results :=
  ⟨tag :: bodyArgs, .base (.gamma 0),
    .cons (.output 0 .head) (.cons (.arg .head) (.cons (.arg (.tail .head))
      (.cons (.arg (.tail (.tail .head))) (.cons (.output 0 (.tail .head)) .nil)))),
    Fin.cases [] (fun _ => [[word], results])⟩

private def body : NestedTheta.Term (Instruction Op) bodyArgs [] [bumpResult, results] results :=
  .bind bumpNode (fun i => i.elim0) <|
    .bind select (Fin.cases stop (fun _ => recurse)) <| .ret (forwarding bodyArgs [bumpResult] results)

private def member : LambdaTerm Op [callable] [] fn :=
  ⟨[callable], .cons (.arg .head) .nil, [bumpResult, results], body⟩

private abbrev address : T := .value (.global (.data ()))

private def group {past : List (Ports T)} : PhiTerm Op [word] past [fn] :=
  ⟨[], .nil, .cons member .nil⟩

private def delta {past : List (Ports T)} : DeltaTerm Op [word] past (.data ()) :=
  ⟨[word], .cons (.arg .head) .nil, [], .ret (.cons (.arg .head) .nil)⟩

private def left : OmegaTerm Op [word] [address, callable] [[address], [callable]] :=
  ⟨.bind (.delta delta) <| .bind (.phi group) <|
    .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))⟩

private def right : OmegaTerm Op [word] [address, callable] [[callable], [address]] :=
  ⟨.bind (.phi group) <| .bind (.delta delta) <|
    .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil))⟩

private def imports : Tuple machine.Val [word] := .cons (.data (42 : Nat)) .nil

private def inputs (mode : Fin 2) (n : Nat) : Tuple machine.Val fn.args :=
  .cons (.control mode) (.cons (.data (7 : Nat)) (.cons (.state n) .nil))

private def start (mode : Fin 2) (n : Nat) : Activation machine results :=
  exported machine 17 left.toGraph imports (.tail .head) (inputs mode n)

private def entry (mode : Fin 2) (n : Nat) : Tuple machine.Val bodyArgs :=
  .cons (start mode n).callee (inputs mode n)

private def answer (n : Nat) : Tuple machine.Val results :=
  .cons (.data (7 : Nat)) (.cons (.state n) .nil)

private theorem inspect_selected (mode : Fin 2) (n : Nat) :
    inspect machine (start mode n) =
      if mode = 1 ∨ n < 2 then .enter (start mode (n + 1)) else .returned (answer (n + 1)) := by
  change exposeTerm machine body.toGraph.toTerm (entry mode n) PUnit.unit = _
  rw [NestedTheta.Term.toTerm_toGraph]
  by_cases continues : mode = 1 ∨ n < 2
  · rw [ite_eq_left continues]
    apply (exposes_iff _ _ _ (by simp)).2
    apply Executes.primitive
    apply Executes.gamma (tag := .control 1) (arguments := entry mode (n + 1))
    · change Tuple.cons (.control (if mode = 1 ∨ n < 2 then 1 else 0)) (entry mode (n + 1)) = _
      rw [ite_eq_left continues]
    · exact .primitive (.apply rfl)
  · rw [ite_eq_right continues]
    apply (exposes_iff _ _ _ (by simp)).2
    apply Executes.primitive
    apply Executes.gamma (tag := .control 0) (arguments := entry mode (n + 1))
    · change Tuple.cons (.control (if mode = 1 ∨ n < 2 then 1 else 0)) (entry mode (n + 1)) = _
      rw [ite_eq_right continues]
    · exact .ret _ _ _

private theorem advance (n : Nat) : Step machine (start 1 n) (start 1 (n + 1)) := by
  exact (inspect_selected 1 n).trans (ite_eq_left (Or.inl rfl))

private theorem unbounded : Diverges machine (start 1 0) :=
  ⟨start 1, rfl, advance⟩

example : InfiniteTrace (Enters machine) (start 1 0) :=
  diverges_iff_enters.mp unbounded

example : ∀ output, ¬ Returns machine (start 1 0).job output :=
  diverges_no_return unbounded

private theorem finite_path : Relation.ReflTransGen (Step machine) (start 0 0) (start 0 2) :=
  let first : Step machine (start 0 0) (start 0 1) :=
    (inspect_selected 0 0).trans (ite_eq_left (Or.inr (by decide)))
  let second : Step machine (start 0 1) (start 0 2) :=
    (inspect_selected 0 1).trans (ite_eq_left (Or.inr (by decide)))
  (Relation.ReflTransGen.single first).tail second

private theorem finished : inspect machine (start 0 2) = .returned (answer 3) :=
  (inspect_selected 0 2).trans (ite_eq_right (by decide))

example : ∀ output, Returns machine (start 0 0).job output ↔ output = answer 3 :=
  fun output => (trace_returns_iff finite_path output).trans (returned_iff finished)

example : (start 0 0).run 0 2 = none := by cbv

example : (start 0 0).run 0 3 = some (answer 3) := by cbv

private theorem supported : SupportedFrom machine (start 1 0) := by
  intro next path
  have reached : ∃ n, next = start 1 n := by
    induction path with
    | refl => exact ⟨0, rfl⟩
    | tail _ step ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, step_deterministic step (advance n)⟩
  obtain ⟨n, rfl⟩ := reached
  rw [show inspect machine (start 1 n) = .enter (start 1 (n + 1)) from advance n]
  simp

private def swapFn : Fin 2 → Fin 2 := Fin.cases 1 (fun _ => 0)

private def swap : Fin 2 ≃ Fin 2 :=
  let inverse : ∀ i, swapFn (swapFn i) = i := Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  ⟨swapFn, swapFn, inverse, inverse⟩

private theorem stopIso : NestedTheta.Graph.Isomorphic (Instruction Op) stop.toGraph stop.toGraph :=
  .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0) rfl (fun i => i.elim0)

private theorem recurseIso : NestedTheta.Graph.Isomorphic (Instruction Op) recurse.toGraph recurse.toGraph :=
  .intro rfl rfl (Equiv.refl _) (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
    (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))) rfl
    (Fin.cases (fun i => i.elim0) (Fin.cases (fun i => i.elim0) (fun i => i.elim0)))

private theorem bodyIso : NestedTheta.Graph.Isomorphic (Instruction Op) body.toGraph body.toGraph :=
  .intro rfl rfl (Equiv.refl _) (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
    (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))) rfl
    (Fin.cases (fun i => i.elim0)
      (Fin.cases (Fin.cases stopIso (Fin.cases recurseIso (fun i => i.elim0))) (fun i => i.elim0)))

private theorem modulesIso : left.toGraph.RenumberedBy right.toGraph swap :=
  (left.renumberedBy_toGraph_iff right swap).2
    ⟨Fin.cases
      (.delta ⟨⟨rfl, rfl⟩, .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0)
        rfl (fun i => i.elim0)⟩)
      (Fin.cases (.phi ⟨⟨rfl, rfl⟩, Fin.cases ⟨⟨rfl, rfl⟩, bodyIso⟩ (fun i => i.elim0)⟩)
        (fun i => i.elim0)), rfl⟩

private def ids : GlobalRel :=
  fun l r => l.1 = 17 ∧ r.1 = 39 ∧ renameVertex swap l.2 = r.2

private theorem compatible : PrimitivesRespect machine ids := by
  intro ins outs opcode l r inputs
  cases opcode with
  | copy => exact inputs
  | bump =>
    cases inputs with
    | cons mode rest =>
      cases rest with
      | cons state tail =>
        cases tail
        cases mode with
        | control mode =>
          cases state with
          | state n => exact .cons (.control _) (.cons (.state ((show Nat from n) + 1)) .nil)

example : Diverges machine (exported machine 39 right.toGraph imports (.tail .head) (inputs 1 0)) := by
  exact (exported_diverges_iff compatible 17 39 modulesIso
    (fun i _ => ⟨rfl, rfl, by
      change renameVertex swap i.val = (swap i).val
      rw [renameVertex, dite_eq_left (show i.val < 2 from i.isLt)]
      rfl⟩) (.cons (.data _) .nil) (.tail .head)
    (.cons (.control 1) (.cons (.data _) (.cons (.state _) .nil))) supported supported).1 unbounded

private def ignoredCall : NestedTheta.Term (Instruction Op) bodyArgs [] [[word], results] results :=
  .bind copyNode (fun i => i.elim0) <| .bind callNode (fun i => i.elim0) <|
    .ret (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))

private def outOfSlice : Activation machine results :=
  ⟨fn.args, .closure (.cons (start 0 0).callee .nil) ignoredCall.toGraph, inputs 0 0⟩

private theorem unsupported : inspect machine outOfSlice = .unsupported := by
  change exposeTerm machine ignoredCall.toGraph.toTerm (entry 0 0) PUnit.unit = _
  rw [NestedTheta.Term.toTerm_toGraph]
  unfold ignoredCall
  erw [exposeTerm, exposeTerm, inTail]
  apply dite_eq_right
  intro forwards
  cases forwards

example : ¬ Diverges machine outOfSlice := unsupported_no_divergence unsupported

example : outOfSlice.run 0 4 = some (answer 0) := by cbv

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Tests
