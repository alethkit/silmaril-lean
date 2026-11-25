module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Tests

private abbrev T := Ty Unit Unit
private abbrev word : T := .value (.data ())
private abbrev state : T := .state ()
private abbrev values : Ports T := [word, state]
private abbrev tag : T := .control 2
private abbrev loopChoice : Ports T := [tag, tag, word, state]
private abbrev fn : Function Unit Unit := ⟨values, values⟩
private abbrev callable : T := fn.port
private abbrev bodyArgs : Ports T := [callable, callable, word, state]

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | stamp (mark : Nat) : Op values values
  | suffix (mark : Nat) : Op [word, state, state] values
  | thetaRoute : Op values loopChoice

private def machine : Machine Op where
  Data _ := Nat
  State _ := List Nat
  primitive
    | .stamp mark, .cons (.data n) (.cons (.state log) .nil) =>
      .cons (.data (n + mark : Nat)) (.cons (.state (log ++ [mark])) .nil)
    | .suffix mark, .cons (.data n) (.cons (.state log) (.cons (.state saved) .nil)) =>
      .cons (.data (n + mark : Nat)) (.cons (.state (log ++ [mark, saved.length])) .nil)
    | .thetaRoute, .cons (.data n) (.cons (.state log) .nil) =>
      let first := n == 0
      .cons (.control (if first then 0 else 1)) <| .cons (.control (if first then 1 else 0)) <|
        .cons (.data (if first then (1 : Nat) else 0)) (.cons (.state (log ++ [if first then 7 else 8])) .nil)

private def args (n : Nat) (log : List Nat) : Tuple machine.Val values :=
  .cons (.data n) (.cons (.state log) .nil)

private def helperNode : NestedTheta.Node (Instruction Op) values [] values :=
  ⟨values, .base (.simple (.primitive (.stamp 1))),
    .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), fun i => i.elim0⟩

private def helper : LambdaTerm Op [callable, callable, callable] [] fn :=
  ⟨[], .nil, [values], .bind helperNode (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))⟩

private def helperCall : NestedTheta.Node (Instruction Op) bodyArgs [] values :=
  ⟨callable :: values, .base (.simple (.apply fn)),
    .cons (.arg .head) (.cons (.arg (.tail (.tail .head)))
      (.cons (.arg (.tail (.tail (.tail .head)))) .nil)), fun i => i.elim0⟩

private def stampNode (mark : Nat) : NestedTheta.Node (Instruction Op) bodyArgs [values] values :=
  ⟨values, .base (.simple (.primitive (.stamp mark))),
    .cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil), fun i => i.elim0⟩

private def mutualCall : NestedTheta.Node (Instruction Op) bodyArgs [values, values] values :=
  ⟨callable :: values, .base (.simple (.apply fn)),
    .cons (.arg (.tail .head)) (.cons (.output (1 : Fin 2) .head)
      (.cons (.output (1 : Fin 2) (.tail .head)) .nil)), fun i => i.elim0⟩

private def suffixNode (mark : Nat) : NestedTheta.Node (Instruction Op) bodyArgs [values, values, values] values :=
  ⟨[word, state, state], .base (.simple (.primitive (.suffix mark))),
    .cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head))
      (.cons (.output (1 : Fin 3) (.tail .head)) .nil)), fun i => i.elim0⟩

private def suffix (mark : Nat) :
    NestedTheta.Term (Instruction Op) bodyArgs [values, values, values] [values] values :=
  .bind (suffixNode mark) (fun i => i.elim0)
    (.ret (.cons (.output (3 : Fin 4) .head) (.cons (.output (3 : Fin 4) (.tail .head)) .nil)))

private def afterHelper (mark : Nat) :
    NestedTheta.Term (Instruction Op) bodyArgs [values] [values, values, values] values :=
  .bind (stampNode mark) (fun i => i.elim0) <| .bind mutualCall (fun i => i.elim0) (suffix mark)

private def body (mark : Nat) :
    NestedTheta.Term (Instruction Op) bodyArgs [] [values, values, values, values] values :=
  .bind helperCall (fun i => i.elim0) (afterHelper mark)

private def member {past : List (Ports T)}
    (first other : Origin [callable, callable, callable] past callable) (mark : Nat) :
    LambdaTerm Op [callable, callable, callable] past fn :=
  ⟨[callable, callable], .cons first (.cons other .nil), _, body mark⟩

private def group : PhiTerm Op [] [] [fn, fn, fn] :=
  ⟨[], .nil, .cons helper <|
    .cons (member (.arg .head) (.arg (.tail (.tail .head))) 10) <|
    .cons (member (.output (0 : Fin 2) .head) (.output (1 : Fin 2) .head) 20) .nil⟩

private def linked : OmegaTerm Op [] [callable, callable, callable] [[callable, callable, callable]] :=
  ⟨.bind (.phi group) <| .ret (.cons (.output (0 : Fin 1) .head)
    (.cons (.output (0 : Fin 1) (.tail .head)) (.cons (.output (0 : Fin 1) (.tail (.tail .head))) .nil)))⟩

private def exports : Tuple machine.Val [callable, callable, callable] :=
  Recursive.linkGraph machine 41 linked.toGraph .nil

private def helperRef : machine.Val callable := exports.get .head

private def memberRef : Bool → machine.Val callable
  | false => exports.get (.tail .head)
  | true => exports.get (.tail (.tail .head))

private def marker (second : Bool) : Nat := if second then 20 else 10

private def entry (second : Bool) (n : Nat) (log : List Nat) : Entry machine :=
  ⟨values, ⟨values, memberRef second, args n log⟩⟩

private def openedArgs (second : Bool) (n : Nat) (log : List Nat) : Tuple machine.Val bodyArgs :=
  .cons helperRef (.cons (memberRef (!second)) (args n log))

private def pending (second : Bool) (n : Nat) (log : List Nat) : Pending machine values values :=
  .bind (past := [values, values]) (suffix (marker second))
    (openedArgs second n log)
    (args (n + 1) (log ++ [1]), (args (n + 1 + marker second) ((log ++ [1]) ++ [marker second]), PUnit.unit))
    .empty

private theorem helperReturns (n : Nat) (log : List Nat) :
    Returns machine (.call helperRef (args n log)) (args (n + 1) (log ++ [1])) :=
  (Recursive.call_iff machine helperRef (args n log) _).2 ⟨0, 1, by cbv⟩

private theorem opened (second : Bool) (n : Nat) (log : List Nat) :
    (entry second n log).openBody =
      .region (body (marker second)) (openedArgs second n log) (PUnit.unit : Locals machine.Val []) := by
  cases second with
  | false => exact congrArg (fun term => Job.region (m := machine) (past := [])
      term (openedArgs false n log) PUnit.unit) (NestedTheta.Term.toTerm_toGraph (body 10))
  | true => exact congrArg (fun term => Job.region (m := machine) (past := [])
      term (openedArgs true n log) PUnit.unit) (NestedTheta.Term.toTerm_toGraph (body 20))

private theorem reaches (second : Bool) (n : Nat) (log : List Nat) :
    Prefix machine (entry second n log).openBody
      (entry (!second) (n + 1 + marker second) ((log ++ [1]) ++ [marker second])) (pending second n log) := by
  rw [opened]
  refine Prefix.later (node := helperCall) (.apply (helperReturns n log)) ?_
  refine Prefix.later (node := stampNode (marker second)) (.primitive (Op.stamp (marker second)) _ _ _) ?_
  exact Prefix.inside (node := mutualCall) (.apply (memberRef (!second)) _)

private def activations : Nat → Bool × Nat × List Nat
  | 0 => (false, 0, [])
  | n + 1 =>
    let previous := activations n
    (!previous.1, previous.2.1 + 1 + marker previous.1, (previous.2.2 ++ [1]) ++ [marker previous.1])

private def descent : Run machine where
  entry n := entry (activations n).1 (activations n).2.1 (activations n).2.2
  pending n := pending (activations n).1 (activations n).2.1 (activations n).2.2
  reaches n := reaches (activations n).1 (activations n).2.1 (activations n).2.2

-- Each selected recursive call occurs after the helper has returned with its
-- own state update. The A and B suffixes and their saved locals remain pending.
private theorem twoFrames :
    descent.stackAt (final := values) .halt 2 =
      (pending true 11 [1, 10]).push ((pending false 0 []).push .halt) := rfl

example : (descent.entry 2) = entry false 32 [1, 10, 1, 20] := rfl

private theorem nextAt (second : Bool) (n : Nat) (log : List Nat) (stack : Stack machine values values) :
    State.runFor 14 ((entry second n log).state stack) =
      (entry (!second) (n + 1 + marker second) ((log ++ [1]) ++ [marker second])).state
        ((pending second n log).push stack) := by
  change State.runFor 13 (.eval (entry second n log).openBody stack) = _
  rw [opened]
  cbv

private theorem runFor_add (first last : Nat) (initial : State machine values) :
    State.runFor (first + last) initial = State.runFor last (State.runFor first initial) := by
  induction first generalizing initial with
  | zero => rw [Nat.zero_add]; rfl
  | succ first ih =>
    rw [Nat.succ_add, State.runFor, State.runFor]
    cases next : initial.next with
    | none => cases last <;> simp only [State.runFor, next]
    | some following => exact ih following

example : State.runFor 28 (start (.call (memberRef false) (args 0 []))) =
    (descent.entry 2).state (descent.stackAt (final := values) .halt 2) := by
  let base : Stack machine values values := .halt
  have schedule := runFor_add 14 14 ((entry false 0 []).state base)
  have first := congrArg (fun state : State machine values => State.runFor 14 state) (nextAt false 0 [] base)
  have second := nextAt true 11 [1, 10] ((pending false 0 []).push base)
  have exactFrames := congrArg (fun stack : Stack machine values values =>
    (entry false 32 [1, 10, 1, 20]).state stack) twoFrames.symm
  exact schedule.trans (first.trans (second.trans exactFrames))

example : ∃ micro positions, Checkpoints descent (final := values) .halt micro positions :=
  descent.checkpoints .halt

example : InfiniteTrace Step (start (.call (memberRef false) (args 0 []))) :=
  descent.infinite .halt

private theorem trace_runFor {micro : Nat → State machine values} {initial : State machine values}
    (started : micro 0 = initial) (steps : ∀ n, Step (micro n) (micro (n + 1))) (i : Nat) :
    micro i = State.runFor i initial := by
  induction i with
  | zero => exact started
  | succ i ih =>
    rw [show i + 1 = i + (1 : Nat) from rfl, runFor_add, ← ih, State.runFor]
    rw [show (micro i).next = some (micro (i + 1)) from steps i]
    rfl

private def firstCall : State machine values := (entry false 0 []).state .halt

private def flags : State machine values → Bool × Bool
  | .returned _ .halt => (true, false)
  | .eval (.call ..) _ | .eval (.iteration ..) _ => (false, true)
  | _ => (false, false)

private theorem firstSegmentFlags :
    ∀ i : Fin 14, flags (State.runFor i.val firstCall) = (false, i.val == 0 || i.val == 3) := by
  decide

private def helperFrame : Stack machine values values :=
  .resume (past := []) (afterHelper 10) (openedArgs false 0 []) PUnit.unit .halt

private theorem helperEntry : State.runFor 3 firstCall =
    .eval (.call helperRef (args 0 [])) helperFrame := by
  change State.runFor 2 (.eval (entry false 0 []).openBody .halt) = _
  rw [opened]
  rfl

private theorem helperReturn : State.runFor 8 firstCall = .returned (args 1 [1]) helperFrame := by
  change State.runFor 7 (.eval (entry false 0 []).openBody .halt) = _
  rw [opened]
  cbv

-- Reflect independent Returns for the helper from a first-entry interval
-- of the actual infinite run, rather than supplying the prefix derivation.
example : ∃ saved, Prefix machine (entry false 0 []).openBody (entry true 11 [1, 10]) saved ∧
    saved.push (.halt : Stack machine values values) = (pending false 0 []).push .halt := by
  obtain ⟨micro, started, steps⟩ := descent.infinite (final := values) .halt
  have agrees := trace_runFor (initial := firstCall) started steps
  have observed (i : Nat) (within : i < 14) :
      flags (micro i) = (false, i == 0 || i == 3) :=
    (congrArg flags (agrees i)).trans (firstSegmentFlags ⟨i, within⟩)
  have live : BeforeReturn micro 1 14 (.halt : Stack machine values values) := by
    rintro i _ within ⟨result, returned⟩
    have checked := observed i within
    rw [returned] at checked
    exact Bool.noConfusion (congrArg Prod.fst checked)
  have earlier : EarlierJobsReturn micro 1 14 := by
    intro i lower within ports job stack entered boundary
    have marked : (flags (micro i)).2 = true := by
      rw [entered]
      cases job <;> cases boundary <;> rfl
    have checked := (congrArg Prod.snd (observed i within)).symm.trans marked
    have index : i = 3 := by
      rcases Bool.or_eq_true_iff.mp checked with zero | three
      · have := beq_iff_eq.mp zero
        omega
      · exact beq_iff_eq.mp three
    subst i
    have exactEntry := entered.symm.trans ((agrees 3).trans helperEntry)
    cases exactEntry
    exact ⟨8, by decide, by decide, args 1 [1], (agrees 8).trans helperReturn⟩
  exact entry_of_interval steps started ((agrees 14).trans (nextAt false 0 [] .halt))
    (by decide) live earlier

private abbrev carried : Ports T := callable :: values
private abbrev loopResult := Theta.BodyResults carried

private def routeNode : NestedTheta.Node (Instruction Op) carried [] loopChoice :=
  ⟨values, .base (.simple (.primitive .thetaRoute)),
    .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil), fun i => i.elim0⟩

private def loopGamma : NestedTheta.Node (Instruction Op) carried [loopChoice] loopResult :=
  ⟨tag :: loopResult, .base (.gamma 0),
    .cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head))
      (.cons (.arg .head) (.cons (.output (0 : Fin 1) (.tail (.tail .head)))
        (.cons (.output (0 : Fin 1) (.tail (.tail (.tail .head)))) .nil)))),
    Fin.cases [] (fun _ => [values, values])⟩

private def loopApply : NestedTheta.Node (Instruction Op) loopResult [] values :=
  ⟨carried, .base (.simple (.apply fn)),
    .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head)))
      (.cons (.arg (.tail (.tail (.tail .head)))) .nil)), fun i => i.elim0⟩

private def loopSuffixNode : NestedTheta.Node (Instruction Op) loopResult [values] values :=
  ⟨[word, state, state], .base (.simple (.primitive (.suffix 9))),
    .cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head))
      (.cons (.arg (.tail (.tail (.tail .head)))) .nil)), fun i => i.elim0⟩

private def loopSuffix : NestedTheta.Term (Instruction Op) loopResult [values] [values] loopResult :=
  .bind loopSuffixNode (fun i => i.elim0) <| .ret (.cons (.arg .head) (.cons (.arg (.tail .head))
    (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))

private def loopArm : NestedTheta.Term (Instruction Op) loopResult [] [values, values] loopResult :=
  .bind loopApply (fun i => i.elim0) loopSuffix

private def afterGamma : NestedTheta.Term (Instruction Op) carried [loopChoice, loopResult] [] loopResult :=
  .ret ((NestedTheta.identityPorts loopResult).map fun _ =>
    Origin.output (past := [loopChoice, loopResult]) (1 : Fin 2))

private def thetaBody : NestedTheta.Term (Instruction Op) carried [] [loopChoice, loopResult] loopResult :=
  .bind routeNode (fun i => i.elim0) <| .bind loopGamma
    (Fin.cases (.ret ((NestedTheta.identityPorts loopResult).map fun _ => Origin.arg)) (fun _ => loopArm))
    afterGamma

private def thetaNode : NestedTheta.Node (Instruction Op) carried [] carried :=
  NestedTheta.thetaVertex [loopChoice, loopResult]

private def afterTheta : NestedTheta.Term (Instruction Op) carried [carried] [] values :=
  .ret (.cons (.output (0 : Fin 1) (.tail .head)) (.cons (.output (0 : Fin 1) (.tail (.tail .head))) .nil))

private def thetaMemberBody : NestedTheta.Term (Instruction Op) carried [] [carried] values :=
  .bind thetaNode (fun _ => thetaBody) afterTheta

private def thetaGroup : PhiTerm Op [] [] [fn] :=
  ⟨[], .nil, .cons ⟨[callable], .cons (.arg .head) .nil, [carried], thetaMemberBody⟩ .nil⟩

private def thetaModule : OmegaTerm Op [] [callable] [[callable]] :=
  ⟨.bind (.phi thetaGroup) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def thetaCallee : machine.Val callable :=
  (Recursive.linkGraph machine 43 thetaModule.toGraph .nil).get .head

private def phaseInput (phase : Nat) (log : List Nat) : Tuple machine.Val carried :=
  .cons thetaCallee (args phase log)

private def thetaEntry (log : List Nat) : Entry machine :=
  ⟨values, ⟨values, thetaCallee, args 0 log⟩⟩

private def nextLog (log : List Nat) : List Nat := (log ++ [7]) ++ [8]

private def armInput (log : List Nat) : Tuple machine.Val loopResult :=
  .cons (.control 0) (phaseInput 0 (nextLog log))

private def bodyPending (log : List Nat) : Pending machine values loopResult :=
  .bind (past := [loopChoice]) afterGamma (phaseInput 1 (log ++ [7]))
    (machine.primitive .thetaRoute (args 1 (log ++ [7])), PUnit.unit)
    (.bind (past := []) loopSuffix (armInput log) PUnit.unit .empty)

private def thetaPending (log : List Nat) : Pending machine values values :=
  .bind (past := []) afterTheta (phaseInput 0 log) PUnit.unit (.loop thetaBody (bodyPending log))

private theorem thetaOpened (log : List Nat) :
    (thetaEntry log).openBody =
      .region thetaMemberBody (phaseInput 0 log) (PUnit.unit : Locals machine.Val []) :=
  congrArg (fun term => Job.region (m := machine) (past := []) term (phaseInput 0 log) PUnit.unit)
    (NestedTheta.Term.toTerm_toGraph thetaMemberBody)

private theorem feedback (log : List Nat) :
    Feedback.Iteration thetaBody (phaseInput 0 log) (phaseInput 1 (log ++ [7])) := by
  refine ⟨.control 1, ?_, rfl⟩
  refine Returns.bind (node := routeNode) (.primitive Op.thetaRoute _ _ _) ?_
  refine Returns.bind (node := loopGamma) (Returns.gamma (tag := (0 : Fin 2)) (.ret _ _ _)) ?_
  exact .ret _ _ _

private theorem thetaActive (log : List Nat) :
    Prefix machine (.region thetaBody (phaseInput 1 (log ++ [7])) PUnit.unit)
      (thetaEntry (nextLog log)) (bodyPending log) := by
  refine Prefix.later (node := routeNode) (.primitive Op.thetaRoute _ _ _) ?_
  refine Prefix.inside (node := loopGamma) (Prefix.gamma (tag := (1 : Fin 2)) ?_)
  exact Prefix.inside (node := loopApply) (.apply thetaCallee _)

example (log : List Nat) :
    Prefix machine (.iteration thetaBody (phaseInput 1 (log ++ [7])))
      (thetaEntry (nextLog log)) (.loop thetaBody (bodyPending log)) :=
  .iteration .refl (thetaActive log)

private theorem thetaReaches (log : List Nat) :
    Prefix machine (thetaEntry log).openBody (thetaEntry (nextLog log)) (thetaPending log) := by
  rw [thetaOpened]
  exact Prefix.inside (node := thetaNode)
    (.theta (.iteration (.single (feedback log)) (thetaActive log)))

private def thetaLogs : Nat → List Nat
  | 0 => []
  | n + 1 => nextLog (thetaLogs n)

private def thetaDescent : Run machine where
  entry n := thetaEntry (thetaLogs n)
  pending n := thetaPending (thetaLogs n)
  reaches n := thetaReaches (thetaLogs n)

private theorem thetaStartStep (log : List Nat) (stack : Stack machine values values) :
    State.runFor 1 ((thetaEntry log).state stack) =
      .eval (.region thetaMemberBody (phaseInput 0 log) PUnit.unit) stack :=
  congrArg (fun job : Job machine values => State.eval job stack) (thetaOpened log)

private theorem thetaNextAt (log : List Nat) (stack : Stack machine values values) :
    State.runFor 21 ((thetaEntry log).state stack) =
      (thetaEntry (nextLog log)).state ((thetaPending log).push stack) := by
  refine (runFor_add 1 20 _).trans
    ((congrArg (fun st : State machine values => State.runFor 20 st) (thetaStartStep log stack)).trans ?_)
  cbv

-- The feedback state is present at re-entry, and the new body has fresh locals.
example : State.runFor 14 ((thetaEntry []).state (.halt : Stack machine values values)) =
    .eval (.region thetaBody (phaseInput 1 [7]) PUnit.unit)
      (.loop thetaBody (.resume (past := []) afterTheta (phaseInput 0 []) PUnit.unit .halt)) := by
  refine (runFor_add 1 13 _).trans
    ((congrArg (fun st : State machine values => State.runFor 13 st) (thetaStartStep [] .halt)).trans ?_)
  cbv

-- Two descents retain all four frames per activation in order, with the
-- previous caller's loop still active beneath the newer caller's suffix.
example : State.runFor 42 ((thetaEntry []).state (.halt : Stack machine values values)) =
    (thetaEntry [7, 8, 7, 8]).state (thetaDescent.stackAt (final := values) .halt 2) := by
  let base : Stack machine values values := .halt
  have schedule := runFor_add 21 21 ((thetaEntry []).state base)
  have first := congrArg (fun st : State machine values => State.runFor 21 st) (thetaNextAt [] base)
  have second := thetaNextAt [7, 8] ((thetaPending []).push base)
  exact schedule.trans (first.trans second)

example : ∃ micro positions, Checkpoints thetaDescent (final := values) .halt micro positions :=
  thetaDescent.checkpoints .halt

example : InfiniteTrace Step ((thetaEntry []).state (.halt : Stack machine values values)) :=
  thetaDescent.infinite .halt

example : stackDepth (thetaDescent.stackAt (final := values) .halt 2) = 8 := rfl

private def thetaFirst : State machine values := (thetaEntry []).state .halt

private theorem thetaSegmentFlags :
    ∀ i : Fin 21, let st := State.runFor i.val thetaFirst
      st.result.isSome = false ∧ (Entry.ofState st).isSome = (i.val == 0) := by
  decide

-- The actual prefix passes through one completed feedback even though
-- θ itself has not returned. Reflect the next call and its saved stack.
example : ∃ saved, Prefix machine (thetaEntry []).openBody (thetaEntry [7, 8]) saved ∧
    saved.push (.halt : Stack machine values values) = (thetaPending []).push .halt := by
  obtain ⟨micro, started, steps⟩ := thetaDescent.infinite (final := values) .halt
  have agrees := trace_runFor (initial := thetaFirst) started steps
  have live : BeforeReturn micro 1 21 (.halt : Stack machine values values) := by
    rintro i _ within ⟨output, returned⟩
    have observed := (thetaSegmentFlags ⟨i, within⟩).1
    change (State.runFor i thetaFirst).result.isSome = false at observed
    rw [← agrees i, returned] at observed
    cases observed
  have earlier : EarlierCallsReturn micro 1 21 := by
    intro i lower within params results callee arguments frame entered
    have observed := (thetaSegmentFlags ⟨i, within⟩).2
    change (Entry.ofState (State.runFor i thetaFirst)).isSome = (i == 0) at observed
    rw [← agrees i, entered] at observed
    have zero : i = 0 := beq_iff_eq.mp observed.symm
    omega
  exact entry_of_theta_interval steps started ((agrees 21).trans (thetaNextAt [] .halt))
    (by decide) live earlier

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Tests
