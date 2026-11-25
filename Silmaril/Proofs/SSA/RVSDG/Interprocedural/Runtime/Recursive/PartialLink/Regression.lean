module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Thms
import Silmaril.SSA.RVSDG.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Tests

open Continuation.Partial (Eval Primitives Site)

private abbrev T := Ty Unit Unit
private abbrev number : T := .value (.data ())
private abbrev global : T := .value (.global (.data ()))
private abbrev control : T := .control 2
private abbrev moduleArgs : Ports T := [control]
private abbrev gammaArgs : Ports T := [control, number]
private abbrev secondCaptures : Ports T := [control, global]

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | seed : Op [] [number]
  | increment : Op [global] [number]
  | missing : Op [number] [number]
  | later : Op [global] [number]

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .seed, .nil => .cons (.data 7) .nil
    | .increment, .cons (.global _ _ (.data n)) .nil => .cons (.data (n + 1)) .nil
    | .missing, input => input
    | .later, .cons (.global _ _ (.data n)) .nil => .cons (.data (n + 10)) .nil

private abbrev LaterAction :=
  Tuple machine.Val [global] → StateT Nat _root_.Part (Tuple machine.Val [number])

private def primitives (later : LaterAction) :
    Primitives machine Nat where
  step
    | .seed, input => fun store => .some (machine.primitive .seed input, store + 3)
    | .increment, input => fun store => .some (machine.primitive .increment input, store + 5)
    | .missing, _ => fun _ => .none
    | .later, input => later input

private def numberValue (n : Nat) : Tuple machine.Val [number] := .cons (.data n) .nil

private def globalValue (vertex n : Nat) : Tuple machine.Val [global] :=
  .cons (.global 42 vertex (.data n)) .nil

private def inputs (tag : Fin 2) : Tuple machine.Val moduleArgs := .cons (.control tag) .nil

private def seed : DeltaTerm Op moduleArgs [] (.data ()) :=
  ⟨[], .nil, [[number]],
    .bind ⟨[], .simple .seed, .nil, fun i => i.elim0⟩ (fun i => i.elim0)
      (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def incrementNode : RVSDG.Node Op secondCaptures [] [number] :=
  ⟨[global], .simple .increment, .cons (.arg (.tail .head)) .nil, fun i => i.elim0⟩

private def gammaNode : RVSDG.Node Op secondCaptures [[number]] [number] :=
  ⟨gammaArgs, .gamma 0, .cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil),
    Fin.cases [] (fun _ => [[number]])⟩

private def missingNode : RVSDG.Node Op [number] [] [number] :=
  ⟨[number], .simple .missing, .cons (.arg .head) .nil, fun i => i.elim0⟩

private def afterMissing : RVSDG.Term Op [number] [[number]] [] [number] :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def afterGamma : RVSDG.Term Op secondCaptures [[number], [number]] [] [number] :=
  .ret (.cons (.output (1 : Fin 2) .head) .nil)

private def guarded : DeltaTerm Op moduleArgs [[global]] (.data ()) :=
  ⟨secondCaptures, .cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil),
    [[number], [number]],
    .bind incrementNode (fun i => i.elim0) <| .bind gammaNode
      (Fin.cases (.ret (.cons (.arg .head) .nil))
        (fun _ => .bind missingNode (fun i => i.elim0) afterMissing))
      afterGamma⟩

private def laterInitializer : DeltaTerm Op moduleArgs [[global], [global]] (.data ()) :=
  ⟨[global], .cons (.output (1 : Fin 2) .head) .nil, [[number]],
    .bind ⟨[global], .simple .later, .cons (.arg .head) .nil, fun i => i.elim0⟩ (fun i => i.elim0)
      (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def graph : Omega Op moduleArgs [global, global] [[global], [global], [global]] :=
  OmegaTerm.toGraph ⟨.bind (.delta seed) <| .bind (.delta guarded) <| .bind (.delta laterInitializer) <|
    .ret (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil))⟩

private def missingSite : Site machine :=
  ⟨[number], [number], .missing, fun i => i.elim0, fun i => embed (i.elim0), numberValue 8⟩

private def failure : Failure machine Nat := ⟨42, 1, missingSite, 28⟩

private def runLater : LaterAction :=
  fun input store => .some (machine.primitive .later input, store + 100)

private def exports : Tuple machine.Val [global, global] :=
  .cons (.global 42 1 (.data (8 : Nat))) (.cons (.global 42 2 (.data (18 : Nat))) .nil)

private theorem openInitializer {past : List (Ports T)} (delta : DeltaTerm Op moduleArgs past (.data ()))
    (values : Tuple machine.Val moduleArgs) (locals : Locals machine.Val past) :
    initializerJob delta.toGraph values locals =
      .region (embed delta.initializer) (delta.captures.read values locals) PUnit.unit := by
  simp only [initializerJob, DeltaTerm.toGraph, RVSDG.Term.toTerm_toGraph]

private def seedSite : Site machine :=
  ⟨[], [number], .seed, fun i => i.elim0, fun i => embed (i.elim0), .nil⟩

private def incrementSite : Site machine :=
  ⟨[global], [number], .increment, fun i => i.elim0, fun i => embed (i.elim0), globalValue 0 7⟩

private def laterSite : Site machine :=
  ⟨[global], [number], .later, fun i => i.elim0, fun i => embed (i.elim0), globalValue 1 8⟩

private theorem seedLinks (later : LaterAction) (tag : Fin 2) :
    LinksVertex (primitives later) 42 (inputs tag) (past := []) PUnit.unit (.delta seed.toGraph) 20
      (.linked (globalValue 0 7) 23) := by
  refine LinksDelta.linked (initialized := numberValue 7) ?_
  erw [openInitializer seed (inputs tag) PUnit.unit]
  refine Eval.bind (value := numberValue 7) (middle := 23) ?_ ?_
  · refine Eval.primitive seedSite ?_
    exact _root_.Part.mem_some _
  · exact .ret _ _ _ _

private theorem guardSucceeds :
    LinksVertex (primitives runLater) 42 (inputs 0) (past := [[global]]) (globalValue 0 7, PUnit.unit)
      (.delta guarded.toGraph) 23 (.linked (globalValue 1 8) 28) := by
  refine LinksDelta.linked (initialized := numberValue 8) ?_
  erw [openInitializer guarded (inputs 0) (globalValue 0 7, PUnit.unit)]
  refine Eval.bind (value := numberValue 8) (middle := 28) ?_ ?_
  · refine Eval.primitive incrementSite ?_
    exact _root_.Part.mem_some _
  · exact .bind (.gamma (tag := (0 : Fin 2)) (.ret _ _ _ _)) (.ret _ _ _ _)

private def pending : Continuation.Descent.Pending machine [number] [number] :=
  .bind (past := [[number]]) (embed afterGamma) (.cons (.control 1) (globalValue 0 7))
    (numberValue 8, PUnit.unit) <|
  .bind (past := []) (embed afterMissing) (numberValue 8) PUnit.unit .empty

private theorem guardBlocks (later : LaterAction) :
    LinksVertex (primitives later) 42 (inputs 1) (past := [[global]]) (globalValue 0 7, PUnit.unit)
      (.delta guarded.toGraph) 23 (.undefined failure) := by
  refine LinksDelta.undefined (pending := pending) ?_
  erw [openInitializer guarded (inputs 1) (globalValue 0 7, PUnit.unit)]
  refine Eval.bind (value := numberValue 8) (middle := 28) ?_ ?_
  · refine Eval.primitive incrementSite ?_
    exact _root_.Part.mem_some _
  · exact .bindBlocked (.gamma (tag := (1 : Fin 2))
      (.bindBlocked (.primitiveBlocked missingSite 28 rfl)))

-- The undefined arm is skipped. The following δ runs and contributes +100
-- to the observed store, and both exported global identities are retained.
private theorem linkSucceeds : Links (primitives runLater) 42 graph (inputs 0) 20 (.linked exports 128) := by
  refine .bind (seedLinks runLater 0) (.bind guardSucceeds ?_)
  refine .bind (values := globalValue 2 18) (middle := 128) ?_ (.ret _ _ _ _)
  refine LinksDelta.linked (initialized := numberValue 18) ?_
  change Eval _ (initializerJob laterInitializer.toGraph _ _) _ _
  rw [openInitializer]
  refine Eval.bind (value := numberValue 18) (middle := 128) ?_ ?_
  · refine Eval.primitive laterSite ?_
    exact _root_.Part.mem_some _
  · exact .ret _ _ _ _

-- The diagnostic is independent of the later action, even if that action
-- would also be undefined. The successful seed and increment still ran.
private theorem linkBlocks (later : LaterAction) :
    Links (primitives later) 42 graph (inputs 1) 20 (.undefined failure) :=
  .bind (seedLinks later 1) (.stop (guardBlocks later))

example :
    link (primitives runLater) 42 graph (inputs 0) 20 = .linked exports 128 :=
  outcome_unique link_spec linkSucceeds

example (later : LaterAction) :
    link (primitives later) 42 graph (inputs 1) 20 = .undefined failure :=
  outcome_unique link_spec (linkBlocks later)

example :
    (primitives runLater).step .missing (numberValue 8) 28 = _root_.Part.none :=
  (undefined_action (linkBlocks runLater)).2.2

example : link (Primitives.liftTotal machine Nat) 42 graph (inputs 1) 20 = .linked exports 20 :=
  link_total.trans (by rfl)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Tests
