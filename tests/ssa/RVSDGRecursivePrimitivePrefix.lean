module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Thms
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

private def bumpNode {past : List (Ports T)} : NestedTheta.Node (Instruction Op) bodyArgs past bumpResult :=
  ⟨bumpResult, .base (.simple (.primitive .bump)),
    .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail (.tail .head)))) .nil), fun i => i.elim0⟩

private def select {past : List (Ports T)} (choice : Origin bodyArgs past tag)
    (dataIn : Origin bodyArgs past word) (stateIn : Origin bodyArgs past state) :
    NestedTheta.Node (Instruction Op) bodyArgs past results :=
  ⟨tag :: bodyArgs, .base (.gamma 0),
    .cons choice (.cons (.arg .head) (.cons (.arg (.tail .head))
      (.cons dataIn (.cons stateIn .nil)))),
    Fin.cases [] (fun _ => [[word], results])⟩

private def body : NestedTheta.Term (Instruction Op) bodyArgs [] [[word], bumpResult, results] results :=
  .bind copyNode (fun i => i.elim0) <| .bind bumpNode (fun i => i.elim0) <|
    .bind (select (.output (1 : Fin 2) .head) (.output (0 : Fin 2) .head) (.output (1 : Fin 2) (.tail .head)))
      (Fin.cases stop (fun _ => recurse)) <| .ret (forwarding bodyArgs [[word], bumpResult] results)

private def bodyR : NestedTheta.Term (Instruction Op) bodyArgs [] [bumpResult, [word], results] results :=
  .bind bumpNode (fun i => i.elim0) <| .bind copyNode (fun i => i.elim0) <|
    .bind (select (.output (0 : Fin 2) .head) (.output (1 : Fin 2) .head) (.output (0 : Fin 2) (.tail .head)))
      (Fin.cases stop (fun _ => recurse)) <| .ret (forwarding bodyArgs [bumpResult, [word]] results)

private def member {sigs : List (Ports T)}
    (term : NestedTheta.Term (Instruction Op) bodyArgs [] sigs results) : LambdaTerm Op [callable] [] fn :=
  ⟨[callable], .cons (.arg .head) .nil, sigs, term⟩

private abbrev address : T := .value (.global (.data ()))

private def group {past : List (Ports T)} (definition : LambdaTerm Op [callable] [] fn) :
    PhiTerm Op [word] past [fn] :=
  ⟨[], .nil, .cons definition .nil⟩

private def delta {past : List (Ports T)} : DeltaTerm Op [word] past (.data ()) :=
  ⟨[word], .cons (.arg .head) .nil, [], .ret (.cons (.arg .head) .nil)⟩

private def left : OmegaTerm Op [word] [address, callable] [[address], [callable]] :=
  ⟨.bind (.delta delta) <| .bind (.phi (group (member body))) <|
    .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))⟩

private def right : OmegaTerm Op [word] [address, callable] [[callable], [address]] :=
  ⟨.bind (.phi (group (member bodyR))) <| .bind (.delta delta) <|
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
    apply Executes.primitive
    apply Executes.gamma (tag := .control 1) (arguments := entry mode (n + 1))
    · change Tuple.cons (.control (if mode = 1 ∨ n < 2 then 1 else 0)) (entry mode (n + 1)) = _
      rw [ite_eq_left continues]
    · exact .primitive (.apply rfl)
  · rw [ite_eq_right continues]
    apply (exposes_iff _ _ _ (by simp)).2
    apply Executes.primitive
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

private theorem supportedFromSteps (run : Nat → Activation machine results)
    (edges : ∀ n, Step machine (run n) (run (n + 1))) : SupportedFrom machine (run 0) := by
  intro next path
  have reached : ∃ n, next = run n := by
    induction path with
    | refl => exact ⟨0, rfl⟩
    | tail _ step ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, step_deterministic step (edges n)⟩
  obtain ⟨n, rfl⟩ := reached
  rw [show inspect machine (run n) = .enter (run (n + 1)) from edges n]
  simp

private theorem supported : SupportedFrom machine (start 1 0) :=
  supportedFromSteps (start 1) advance

private def startR (n : Nat) : Activation machine results :=
  exported machine 39 right.toGraph imports (.tail .head) (inputs 1 n)

private theorem advanceR (n : Nat) : Step machine (startR n) (startR (n + 1)) := by
  change exposeTerm machine bodyR.toGraph.toTerm (.cons (startR n).callee (inputs 1 n)) PUnit.unit = _
  rw [NestedTheta.Term.toTerm_toGraph]
  exact (exposes_iff _ _ _ (by simp)).2 (.primitive (.primitive (.gamma rfl (.primitive (.apply rfl)))))

private theorem supportedR : SupportedFrom machine (startR 0) :=
  supportedFromSteps startR advanceR

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

private def swapPrefixFn : Fin 3 → Fin 3 :=
  Fin.cases 1 (Fin.cases 0 (fun _ => 2))

private def swapPrefix : Fin 3 ≃ Fin 3 :=
  let inverse : ∀ i, swapPrefixFn (swapPrefixFn i) = i :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  ⟨swapPrefixFn, swapPrefixFn, inverse, inverse⟩

private theorem bodyIso : NestedTheta.Graph.Isomorphic (Instruction Op) body.toGraph bodyR.toGraph :=
  .intro rfl rfl swapPrefix (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))))
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))) rfl
    (Fin.cases (fun i => i.elim0) (Fin.cases (fun i => i.elim0)
      (Fin.cases (Fin.cases stopIso (Fin.cases recurseIso (fun i => i.elim0))) (fun i => i.elim0))))

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

private theorem allocated (i : Fin 2) : ids (17, i.val) (39, (swap i).val) := by
  refine ⟨rfl, rfl, ?_⟩
  change renameVertex swap i.val = (swap i).val
  rw [renameVertex, dite_eq_left i.isLt]

private theorem startsRelated : Activation.Related machine ids (start 1 0) (startR 0) :=
  exported_related compatible 17 39 modulesIso (fun i _ => allocated i)
    (.cons (.data _) .nil) (.tail .head) (.cons (.control 1) (.cons (.data _) (.cons (.state _) .nil)))

/-- A supplied left stream is matched at every index by the other linked
program. The right entry at index n carries exactly state n. -/
example : ∃ run : Nat → Activation machine results, run 0 = startR 0 ∧
    (∀ n, Step machine (run n) (run (n + 1))) ∧
    ∀ n, run n = startR n ∧ Activation.Related machine ids (start 1 n) (run n) := by
  obtain ⟨run, first, edges, paired⟩ := stream_match_right compatible startsRelated supportedR
    (start 1) rfl advance
  have exactRight (n : Nat) : run n = startR n := by
    induction n with
    | zero => exact first
    | succ n ih => exact step_deterministic (ih ▸ edges n) (advanceR n)
  exact ⟨run, first, edges, fun n => ⟨exactRight n, paired n⟩⟩

example : ∃ run : Nat → Activation machine results, run 0 = start 1 0 ∧
    (∀ n, Step machine (run n) (run (n + 1))) ∧
    ∀ n, Activation.Related machine ids (run n) (startR n) :=
  stream_match_left compatible startsRelated supported startR rfl advanceR

example : Diverges machine (startR 0) :=
  (diverges_iff compatible startsRelated supported supportedR).1 unbounded

example : (exported machine 39 right.toGraph imports (.tail .head) (inputs 0 0)).run 0 3 =
    some (answer 3) := by cbv

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

private def savedFrames (n : Nat) (outer : Continuation.Stack machine results results) :
    Continuation.Stack machine results results :=
  let copied : Tuple machine.Val [word] := .cons (.data (7 : Nat)) .nil
  let bumped : Tuple machine.Val bumpResult :=
    .cons (.control (1 : Fin 2)) (.cons (.state (n + 1)) .nil)
  .resume (past := [[word]]) (.ret (forwarding bodyArgs [[word]] results)) (entry 1 (n + 1))
    (copied, PUnit.unit)
    (.resume (past := [[word], bumpResult]) (.ret (forwarding bodyArgs [[word], bumpResult] results))
      (entry 1 n) (copied, bumped, PUnit.unit) outer)

open Continuation.TailCall (callState) in
example : Continuation.State.runFor 14 (callState (start 1 0) .halt) =
    callState (start 1 1) (savedFrames 0 .halt) := by cbv

open Continuation.TailCall (callState) in
example : Continuation.State.runFor 28 (callState (start 1 0) .halt) =
    callState (start 1 2) (savedFrames 1 (savedFrames 0 .halt)) := by cbv

open Continuation.TailCall (callState IsCall) in
example : ∃ (framesAt : Nat → Continuation.Stack machine results results)
    (micro : Nat → Continuation.State machine results) (indices : Nat → Nat),
    framesAt 0 = .halt ∧ indices 0 = 0 ∧
    (∀ n, Continuation.Step (micro n) (micro (n + 1))) ∧
    (∀ n, indices n < indices (n + 1)) ∧
    (∀ n, micro (indices n) = callState (start 1 n) (framesAt n)) ∧
    (∀ n j, indices n < j → j < indices (n + 1) → ¬ IsCall (micro j)) ∧
    ∀ n, Step machine (start 1 n) (start 1 (n + 1)) := by
  obtain ⟨framesAt, empty, forwards, segments⟩ :=
    Continuation.TailCall.stream_segments (start 1) advance (.base (base := .halt))
  obtain ⟨micro, indices, first, edges, rising, hits, inside⟩ :=
    Continuation.TailCall.segments_microsteps (fun n => callState (start 1 n) (framesAt n)) segments
  have sliced := Continuation.TailCall.microsteps_segments micro indices edges rising
    (fun n => (hits n).symm ▸ True.intro) inside
  have tailSegments (n : Nat) : Continuation.TailCall.CallSegment
      (callState (start 1 n) (framesAt n)) (callState (start 1 (n + 1)) (framesAt (n + 1))) :=
    (hits n) ▸ (hits (n + 1)) ▸ sliced n
  have admitted (n : Nat) : inspect machine (start 1 n) ≠ .unsupported := by
    rw [show inspect machine (start 1 n) = .enter (start 1 (n + 1)) from advance n]
    simp
  exact ⟨framesAt, micro, indices, empty, first, edges, rising, hits, inside,
    Continuation.TailCall.steps_of_segments (start 1) framesAt forwards admitted tailSegments⟩

open Continuation.TailCall (callState CallSegment) in
example (next : Activation machine results) (parked : Continuation.Stack machine results results) :
    ¬ CallSegment (callState (start 0 2) .halt) (callState next parked) := by
  intro segment
  have admitted : inspect machine (start 0 2) ≠ .unsupported := by rw [finished]; simp
  have entered := Continuation.TailCall.step_of_segment .base admitted segment
  cases finished.symm.trans entered

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Tests
