module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tests

private abbrev T := Ty Unit Unit
private abbrev word : T := .value (.data ())
private abbrev address : T := .value (.global (.data ()))
private abbrev st : T := .state ()
private abbrev resultPorts : Ports T := [word, st]
private abbrev fn : Function Unit Unit := ⟨[st], resultPorts⟩
private abbrev callable : T := fn.port
private abbrev groupPorts : Ports T := [callable, callable]
private abbrev bodyInput : Ports T := [address, callable, st]
private abbrev branchInput : Ports T := [word, callable, st]
private abbrev stepped : Ports T := [.control 2, st]

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | add (increment : Nat) : Op [word] [word]
  | load : Op [address] [word]
  | step : Op [st] stepped

private def machine : Machine Op where
  Data _ := Nat
  State _ := Nat
  primitive
    | .add increment, .cons (.data n) .nil => .cons (.data (n + increment)) .nil
    | .load, .cons (.global _ _ (.data n)) .nil => .cons (.data n) .nil
    | .step, .cons (.state n) .nil =>
      .cons (.control (if n = 0 then 0 else 1)) (.cons (.state (n - 1)) .nil)

private def rotate : Fin 3 ≃ Fin 3 :=
  ⟨Fin.cases 1 (Fin.cases 2 (Fin.cases 0 Fin.elim0)),
   Fin.cases 2 (Fin.cases 0 (Fin.cases 1 Fin.elim0)),
   Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))),
   Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))⟩

private def exchange : Fin 3 → Fin 3 :=
  Fin.cases 1 (Fin.cases 0 (Fin.cases 2 Fin.elim0))

private def swap : Fin 3 ≃ Fin 3 :=
  let inverse : ∀ i, exchange (exchange i) = i :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  ⟨exchange, exchange, inverse, inverse⟩

private def ids : GlobalRel :=
  fun left right => left.1 = 17 ∧ right.1 = 39 ∧ renameVertex rotate left.2 = right.2

private theorem compatible : PrimitivesRespect machine ids := by
  intro ins outs opcode left right related
  cases opcode with
  | add increment =>
    cases related with
    | cons head tail =>
      cases tail
      cases head with
      | data value => exact .cons (.data _) .nil
  | load =>
    cases related with
    | cons head tail =>
      cases tail
      cases head with
      | global identity payload =>
        cases payload with
        | data value => exact .cons (.data _) .nil
  | step =>
    cases related with
    | cons head tail =>
      cases tail
      cases head with
      | state value => exact .cons (.control _) (.cons (.state _) .nil)

private def delta {past : List (Ports T)} (increment : Nat) : DeltaTerm Op [word] past (.data ()) :=
  let node : RVSDG.Node Op [word] [] [word] :=
    ⟨[word], .simple (.add increment), .cons (.arg .head) .nil, fun i => i.elim0⟩
  ⟨[word], .cons (.arg .head) .nil, [[word]],
    .bind node (fun i => Fin.elim0 (show Fin 0 from i))
      (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private abbrev load {past : List (Ports T)} : NestedTheta.Node (Instruction Op) bodyInput past [word] :=
  ⟨[address], .base (.simple (.primitive .load)), .cons (.arg .head) .nil, fun i => i.elim0⟩

private abbrev step {past : List (Ports T)} : NestedTheta.Node (Instruction Op) bodyInput past stepped :=
  ⟨[st], .base (.simple (.primitive .step)), .cons (.arg (.tail (.tail .head))) .nil, fun i => i.elim0⟩

private def stop : NestedTheta.Term (Instruction Op) branchInput [] [] resultPorts :=
  .ret (.cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil))

private def recurse : NestedTheta.Term (Instruction Op) branchInput [] [resultPorts] resultPorts :=
  let call : NestedTheta.Node (Instruction Op) branchInput [] resultPorts :=
    ⟨[callable, st], .base (.simple (.apply fn)),
      .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil), fun i => i.elim0⟩
  .bind call (fun i => Fin.elim0 (show Fin 0 from i))
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private abbrev branch {past : List (Ports T)} (tag : Origin bodyInput past (.control 2))
    (value : Origin bodyInput past word) (state : Origin bodyInput past st) :
    NestedTheta.Node (Instruction Op) bodyInput past resultPorts :=
  ⟨.control 2 :: branchInput, .base (.gamma 0),
    .cons tag (.cons value (.cons (.arg (.tail .head)) (.cons state .nil))),
    Fin.cases [] (fun _ => [resultPorts])⟩

private def bodyL :
    NestedTheta.Term (Instruction Op) bodyInput [] [[word], stepped, resultPorts] resultPorts :=
  .bind load (fun i => Fin.elim0 (show Fin 0 from i))
    (.bind step (fun i => Fin.elim0 (show Fin 0 from i))
      (.bind (branch (.output (1 : Fin 2) .head) (.output (0 : Fin 2) .head)
        (.output (1 : Fin 2) (.tail .head))) (Fin.cases stop fun _ => recurse)
        (.ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil)))))

private def bodyR :
    NestedTheta.Term (Instruction Op) bodyInput [] [stepped, [word], resultPorts] resultPorts :=
  .bind step (fun i => Fin.elim0 (show Fin 0 from i))
    (.bind load (fun i => Fin.elim0 (show Fin 0 from i))
      (.bind (branch (.output (0 : Fin 2) .head) (.output (1 : Fin 2) .head)
        (.output (0 : Fin 2) (.tail .head))) (Fin.cases stop fun _ => recurse)
        (.ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil)))))

private abbrev groupInput := [address, callable, callable]

private def member {past bodySigs : List (Ports T)}
    (other : Origin groupInput past callable)
    (body : NestedTheta.Term (Instruction Op) bodyInput [] bodySigs resultPorts) :
    LambdaTerm Op groupInput past fn :=
  ⟨[address, callable], .cons (.arg .head) (.cons other .nil), bodySigs, body⟩

private def group {past bodySigs : List (Ports T)} (global : Origin [word] past address)
    (body : NestedTheta.Term (Instruction Op) bodyInput [] bodySigs resultPorts) :
    PhiTerm Op [word] past [fn, fn] :=
  ⟨[address], .cons global .nil,
    .cons (member (.arg (.tail (.tail .head))) body)
      (.cons (member (.output (0 : Fin 1) .head) body) .nil)⟩

private abbrev sigsL : List (Ports T) := [[address], groupPorts, [address]]
private abbrev sigsR : List (Ports T) := [[address], [address], groupPorts]
private abbrev exports : Ports T := [address, callable, callable]

private def left : OmegaTerm Op [word] exports sigsL :=
  ⟨.bind (.delta (delta 1)) <|
    .bind (.phi (group (past := [[address]]) (.output (0 : Fin 1) .head) bodyL)) <|
    .bind (.delta (delta 7)) <|
    .ret (.cons (.output (0 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head)
      (.cons (.output (1 : Fin 3) (.tail .head)) .nil)))⟩

private def right : OmegaTerm Op [word] exports sigsR :=
  ⟨.bind (.delta (delta 7)) <|
    .bind (.delta (delta 1)) <|
    .bind (.phi (group (past := [[address], [address]]) (.output (1 : Fin 2) .head) bodyR)) <|
    .ret (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head)
      (.cons (.output (2 : Fin 3) (.tail .head)) .nil)))⟩

private theorem deltaIso (rename : Nat → Nat) (n : Nat) {past past' : List (Ports T)} :
    (delta (past := past) n).Renumbered rename (delta (past := past') n) := by
  refine ⟨⟨rfl, rfl⟩, .intro rfl rfl (Equiv.refl _) ?_ ?_ rfl ?_⟩
  · exact Fin.cases rfl (fun i => i.elim0)
  · exact Fin.cases rfl (fun i => i.elim0)
  · exact Fin.cases (fun j => j.elim0) (fun i => i.elim0)

private theorem stopIso : NestedTheta.Graph.Isomorphic (Instruction Op) stop.toGraph stop.toGraph :=
  .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0) rfl (fun i => i.elim0)

private theorem recurseIso :
    NestedTheta.Graph.Isomorphic (Instruction Op) recurse.toGraph recurse.toGraph := by
  refine .intro rfl rfl (Equiv.refl _) ?_ ?_ rfl ?_
  · exact Fin.cases rfl (fun i => i.elim0)
  · exact Fin.cases rfl (fun i => i.elim0)
  · exact Fin.cases (fun j => j.elim0) (fun i => i.elim0)

private theorem bodyIso : NestedTheta.Graph.Isomorphic (Instruction Op) bodyL.toGraph bodyR.toGraph := by
  refine .intro rfl rfl swap ?_ ?_ rfl ?_
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  · refine Fin.cases (fun j => j.elim0) (Fin.cases (fun j => j.elim0) (Fin.cases ?_ (fun i => i.elim0)))
    exact Fin.cases stopIso (Fin.cases recurseIso (fun i => i.elim0))

private theorem groupsIso :
    (group (past := [[address]]) (.output (0 : Fin 1) .head) bodyL).Renumbered (renameVertex rotate)
      (group (past := [[address], [address]]) (.output (1 : Fin 2) .head) bodyR) :=
  ⟨⟨rfl, rfl⟩, Fin.cases ⟨⟨rfl, rfl⟩, bodyIso⟩ (Fin.cases ⟨⟨rfl, rfl⟩, bodyIso⟩ (fun i => i.elim0))⟩

private theorem termsIso : left.RenumberedBy right rotate :=
  ⟨Fin.cases (.delta (deltaIso _ 1)) (Fin.cases (.phi groupsIso)
    (Fin.cases (.delta (deltaIso _ 7)) (fun i => i.elim0))), rfl⟩

private theorem modulesIso : left.toGraph.RenumberedBy right.toGraph rotate :=
  (left.renumberedBy_toGraph_iff right rotate).2 termsIso

private def imports : Tuple machine.Val [word] := .cons (.data (41 : Nat)) .nil
private def input : Tuple machine.Val [st] := .cons (.state (3 : Nat)) .nil
private theorem importsRelated : TupleRelated machine ids imports imports := .cons (.data _) .nil
private theorem inputRelated : TupleRelated machine ids input input := .cons (.state _) .nil
private def result : Tuple machine.Val resultPorts := .cons (.data (42 : Nat)) (.cons (.state (0 : Nat)) .nil)
private def linkedL : Tuple machine.Val exports := Recursive.linkGraph machine 17 left.toGraph imports
private def linkedR : Tuple machine.Val exports := Recursive.linkGraph machine 39 right.toGraph imports
private def entryPort : Port exports callable := .tail .head

private def allocation (output : Tuple machine.Val exports) : GlobalId × Nat :=
  match output.get .head with
  | .global unit vertex (.data payload) => ((unit, vertex), payload)

example : allocation linkedL = ((17, 0), 42) := by cbv
example : allocation linkedR = ((39, 1), 42) := by cbv
example : invoke machine 0 3 (linkedL.get entryPort) input = none := by cbv
example : invoke machine 0 3 (linkedR.get entryPort) input = none := by cbv
private theorem leftRun : invoke machine 0 4 (linkedL.get entryPort) input = some result := by cbv
example : invoke machine 0 4 (linkedR.get entryPort) input = some result := by cbv

private theorem allocated (i : Fin sigsL.length) :
    ids (17, i.val) (39, (rotate i).val) := by
  have bound : i.val < 3 := i.isLt
  refine ⟨rfl, rfl, ?_⟩
  change renameVertex rotate i.val = (rotate i).val
  simp only [renameVertex, dite_eq_left bound]
  rfl

example : TupleRelated machine ids (Recursive.linkTerm machine 17 left imports)
    (Recursive.linkTerm machine 39 right imports) :=
  Recursive.linkTerm_related compatible 17 39 termsIso (fun i _ => allocated i) importsRelated

example (loops depth : Nat) :
    RunRelated machine ids (invoke machine loops depth (linkedL.get entryPort) input)
      (invoke machine loops depth (linkedR.get entryPort) input) :=
  Recursive.exportedCall_related compatible 17 39 loops depth modulesIso (fun i _ => allocated i)
    importsRelated entryPort inputRelated

private theorem observes (x y : Tuple machine.Val resultPorts) (pair : TupleRelated machine ids x y) :
    x = result ↔ y = result := by
  cases pair with
  | cons value tail =>
    cases value
    cases tail with
    | cons state empty => cases state; cases empty; rfl

example : Returns machine (.call (linkedR.get entryPort) input) result := by
  have preservation := Recursive.exportedCall_returns_iff compatible 17 39 modulesIso (fun i _ => allocated i)
    importsRelated entryPort inputRelated observes
  obtain ⟨out, returns, observed⟩ := preservation.1
    ⟨result, (call_iff machine _ _ _).2 ⟨0, 4, leftRun⟩, rfl⟩
  exact observed ▸ returns

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tests
