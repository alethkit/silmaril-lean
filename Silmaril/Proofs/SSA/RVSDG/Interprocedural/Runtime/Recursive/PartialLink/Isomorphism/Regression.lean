module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Infer.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Tests

open Continuation.Partial (Config Eval Primitives Site)
open Continuation.Partial.Executable (Actions runFor)
open Continuation.Descent (Pending)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev global : T := .value (.global (.data ()))
private abbrev args : Ports T := [num]
private abbrev exports : Ports T := [global, global]

private inductive Op : Dialect (ValueSort Unit Unit) Unit where
  | seed : Op [num] [num]
  | finish : Op [global, num] [num]

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .seed, .cons (.data n) .nil => .cons (.data (n + 7)) .nil
    | .finish, .cons (.global _ _ (.data n)) (.cons (.data _) .nil) => .cons (.data (n + 1)) .nil

private def number (n : Nat) : Tuple machine.Val [num] := .cons (.data n) .nil

private def actions : Actions machine Nat where
  step
    | .seed, .cons (.data n) .nil => fun store => some (number ((show Nat from n) + 7), store + 3)
    | .finish, .cons (.global _ _ (.data n)) (.cons (.data flag) .nil) => fun store =>
      let test : Nat := flag
      if test = 0 then none else some (number ((show Nat from n) + 1), store + 5)

private def primitives : Primitives machine Nat := actions.toPrimitives

private def positions : Fin 3 ≃ Fin 3 :=
  (Equiv.swap 0 1).trans (Equiv.swap 0 2)

private def ids : GlobalRel := fun left right =>
  left.1 = right.1 ∧ renameVertex positions left.2 = right.2

private theorem respects : ActionsRespect primitives ids := by
  intro ins outs opcode left right paired store
  cases opcode with
  | seed =>
    cases paired with
    | cons head tail =>
      cases head with
      | data n =>
        cases tail
        exact .returned (.cons (.data _) .nil) (store + 3)
  | finish =>
    cases paired with
    | cons captured rest =>
      cases captured with
      | global _ payload =>
        cases payload with
        | data n =>
          cases rest with
          | cons head tail =>
            cases head with
            | data flag =>
              cases tail
              let test : Nat := flag
              change ActionRelated machine ids Nat [num]
                (_root_.Part.ofOption (if test = 0 then none else some (number ((show Nat from n) + 1), store + 5)))
                (_root_.Part.ofOption (if test = 0 then none else some (number ((show Nat from n) + 1), store + 5)))
              split
              · exact .undefined
              · exact .returned (.cons (.data _) .nil) (store + 5)

private def seedTerm : Term Op [num] [] [[num]] [num] :=
  .bind ⟨[num], .simple .seed, .cons (.arg .head) .nil, fun i => i.elim0⟩
    (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def finishTail : Term Op [global, num] [[num]] [] [num] :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def finishTerm : Term Op [global, num] [] [[num]] [num] :=
  .bind ⟨[global, num], .simple .finish, .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
      fun i => i.elim0⟩ (fun i => i.elim0) finishTail

private def seedDelta (past : List (Ports T)) : DeltaTerm Op args past (.data ()) :=
  ⟨[num], .cons (.arg .head) .nil, [[num]], seedTerm⟩

private def finishL : DeltaTerm Op args [[global]] (.data ()) :=
  ⟨[global, num], .cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil), [[num]], finishTerm⟩

private def finishR : DeltaTerm Op args [[], [global]] (.data ()) :=
  ⟨[global, num], .cons (.output (1 : Fin 2) .head) (.cons (.arg .head) .nil), [[num]], finishTerm⟩

private def leftTerm : OmegaTerm Op args exports [[global], [global], []] :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.delta finishL) <| .bind (.phi (emptyPhi Op args _)) <|
    .ret (.cons (.output (0 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil))⟩

private def rightTerm : OmegaTerm Op args exports [[], [global], [global]] :=
  ⟨.bind (.phi (emptyPhi Op args [])) <| .bind (.delta (seedDelta [[]])) <| .bind (.delta finishR) <|
    .ret (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil))⟩

private theorem fixedAddresses {n : Nat} (addresses : List Address) :
    addresses.map (Address.rename (renameVertex (Equiv.refl (Fin n)))) = addresses := by
  have fixed (address : Address) : address.rename (renameVertex (Equiv.refl (Fin n))) = address := by
    cases address with
    | arg => rfl
    | output i port =>
      change Address.output (renameVertex (Equiv.refl (Fin n)) i) port = .output i port
      unfold renameVertex
      split <;> rfl
  induction addresses with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, fixed, ih]

private theorem noChildren_refl {ins outs : Ports T} {sigs : List (Ports T)}
    (graph : Graph Op ins [] sigs outs) (empty : ∀ i, (graph.nodes i).shape.regionCount = 0) :
    Graph.Isomorphic Op graph graph := by
  refine .intro rfl rfl (Equiv.refl _) (fun _ => rfl) (fun _ => fixedAddresses _) (fixedAddresses _) ?_
  intro i arm
  exact (Fin.cast (empty i) arm).elim0

private theorem iso : leftTerm.toGraph.RenumberedBy rightTerm.toGraph positions := by
  refine ⟨?_, rfl⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .delta ⟨⟨rfl, rfl⟩, noChildren_refl _ (fun i => Fin.cases rfl (fun j => j.elim0) i)⟩
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact .delta ⟨⟨rfl, rfl⟩, noChildren_refl _ (fun i => Fin.cases rfl (fun j => j.elim0) i)⟩
    · refine Fin.cases ?_ (fun l => l.elim0) k
      exact .phi ⟨⟨rfl, rfl⟩, fun i => i.elim0⟩

private theorem ordered : Ordered Op (renameVertex positions) args exports
    leftTerm.toGraph.toTerm.region rightTerm.toGraph.toTerm.region := by
  rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
  exact .emptyRight (.bind rfl (.delta ⟨rfl, rfl⟩ seedTerm)
    (.bind rfl (.delta ⟨rfl, rfl⟩ finishTerm) (.emptyLeft (.ret _ _))))

private theorem paired (flag : Nat) :
    OutcomesRelated machine ids Nat (renameVertex positions) exports
      (link primitives 73 leftTerm.toGraph (number flag) 20)
      (link primitives 73 rightTerm.toGraph (number flag) 20) :=
  link_related respects iso ordered (fun _ => ⟨rfl, rfl⟩) (.cons (.data flag) .nil) 20

private def globalValue (vertex n : Nat) : machine.Val global := .global 73 vertex (.data n)

private theorem matchingGlobal (vertex value : Nat) {other : machine.Val global}
    (paired : ValueRelated machine ids (globalValue vertex value) other) :
    other = globalValue (renameVertex positions vertex) value := by
  change ValueRelated machine ids (.global 73 vertex (.data value)) other at paired
  cases paired with
  | global identity payload =>
    cases payload with
    | data =>
      obtain ⟨unit, address⟩ := identity
      cases unit
      cases address
      rfl

private def finishInputs (vertex payload flag : Nat) : Tuple machine.Val [global, num] :=
  .cons (globalValue vertex payload) (number flag)

private def finishSite (vertex payload flag : Nat) : Site machine :=
  ⟨[global, num], [num], .finish, fun i => i.elim0, fun i => embed (i.elim0), finishInputs vertex payload flag⟩

private theorem matchingSite {other : Site machine}
    (paired : SitesRelated machine ids (finishSite 0 7 0) other) :
    other = finishSite 1 7 0 := by
  cases paired with
  | same inputs =>
    change TupleRelated machine ids (.cons (globalValue 0 7) (number 0)) _ at inputs
    cases inputs with
    | cons global flag =>
      have address := matchingGlobal 0 7 global
      cases address
      cases flag with
      | cons value tail =>
        cases value
        cases tail
        rfl

private def seedSite (flag : Nat) : Site machine :=
  ⟨[num], [num], .seed, fun i => i.elim0, fun i => embed (i.elim0), number flag⟩

private theorem seedRuns (flag : Nat) :
    Eval primitives (.region (embed seedTerm) (number flag) PUnit.unit) 20 (.returned (number (flag + 7)) 23) := by
  refine Eval.bind (value := number (flag + 7)) (middle := 23) ?_ ?_
  · refine Eval.primitive (seedSite flag) ?_
    exact _root_.Part.mem_some _
  · exact .ret _ _ _ _

private def blockedFrame (vertex : Nat) : Pending machine [num] [num] :=
  .bind (past := []) (embed finishTail) (finishInputs vertex 7 0) PUnit.unit .empty

private theorem finishBlocks (vertex : Nat) :
    Eval primitives (.region (embed finishTerm) (finishInputs vertex 7 0) PUnit.unit) 23
      (.blocked (finishSite vertex 7 0) (blockedFrame vertex) 23) :=
  .bindBlocked (.primitiveBlocked (finishSite vertex 7 0) 23 rfl)

private theorem finishReturns (vertex : Nat) :
    Eval primitives (.region (embed finishTerm) (finishInputs vertex 8 1) PUnit.unit) 23
      (.returned (number 9) 28) := by
  refine Eval.bind (value := number 9) (middle := 28) ?_ ?_
  · refine Eval.primitive (finishSite vertex 8 1) ?_
    exact _root_.Part.mem_some _
  · exact .ret _ _ _ _

private theorem openInitializer {context : Ports T} {sigs : List (Ports T)}
    (term : Term Op context [] sigs [num]) (inputs : Tuple machine.Val context) :
    Job.region (m := machine) (past := []) (embed term.toGraph.toTerm) inputs PUnit.unit =
      .region (embed term) inputs PUnit.unit :=
  congrArg (fun code => Job.region (m := machine) (past := []) (embed code) inputs PUnit.unit)
    (Term.toTerm_toGraph term)

private def failure (δ source : Nat) : Failure machine Nat := ⟨73, δ, finishSite source 7 0, 23⟩

private def readyExports (first second : Nat) : Tuple machine.Val exports :=
  .cons (globalValue first 8) (.cons (globalValue second 9) .nil)

private theorem blockedL : Links primitives 73 leftTerm.toGraph (number 0) 20 (.undefined (failure 1 0)) := by
  refine LinksTable.bind (values := (.cons (globalValue 0 7) .nil : Tuple machine.Val [global]))
    (middle := 23) ?_ (.stop ?_)
  · refine LinksDelta.linked (initialized := number 7) ?_
    change Eval primitives (.region (embed seedTerm.toGraph.toTerm) (number 0) PUnit.unit) _ _
    rw [openInitializer seedTerm (number 0)]
    exact seedRuns 0
  · refine LinksDelta.undefined (pending := blockedFrame 0) ?_
    change Eval primitives (.region (embed finishTerm.toGraph.toTerm) (finishInputs 0 7 0) PUnit.unit) _ _
    rw [openInitializer finishTerm (finishInputs 0 7 0)]
    exact finishBlocks 0

example : link primitives 73 leftTerm.toGraph (number 0) 20 = .undefined (failure 1 0) :=
  outcome_unique link_spec blockedL

-- The first δ ran before the later action blocked. Its allocation and
-- the later δ both moved. The blocked operand still contains the related global.
example : ∃ right, link primitives 73 rightTerm.toGraph (number 0) 20 = .undefined right ∧
    right.vertex = 2 ∧ right.store = 23 ∧ right.site = finishSite 1 7 0 := by
  have related := paired 0
  rw [outcome_unique link_spec blockedL] at related
  generalize link primitives 73 rightTerm.toGraph (number 0) 20 = observed at related ⊢
  cases related with
  | undefined position _ sites store =>
    exact ⟨_, rfl, position.symm, rfl, matchingSite sites⟩

private theorem successL : Links primitives 73 leftTerm.toGraph (number 1) 20 (.linked (readyExports 0 1) 28) := by
  refine LinksTable.bind (values := (.cons (globalValue 0 8) .nil : Tuple machine.Val [global]))
    (middle := 23) ?_ ?_
  · refine LinksDelta.linked (initialized := number 8) ?_
    change Eval primitives (.region (embed seedTerm.toGraph.toTerm) (number 1) PUnit.unit) _ _
    rw [openInitializer seedTerm (number 1)]
    exact seedRuns 1
  · refine LinksTable.bind (values := (.cons (globalValue 1 9) .nil : Tuple machine.Val [global]))
      (middle := 28) ?_ (.bind (values := (.nil : Tuple machine.Val [])) (middle := 28) rfl (.ret _ _ _ _))
    refine LinksDelta.linked (initialized := number 9) ?_
    change Eval primitives (.region (embed finishTerm.toGraph.toTerm) (finishInputs 0 8 1) PUnit.unit) _ _
    rw [openInitializer finishTerm (finishInputs 0 8 1)]
    exact finishReturns 0

example : ∃ right, link primitives 73 rightTerm.toGraph (number 1) 20 = .linked right 28 ∧
    right.get .head = globalValue 1 8 ∧ right.get (.tail .head) = globalValue 2 9 := by
  have related := paired 1
  rw [outcome_unique link_spec successL] at related
  generalize link primitives 73 rightTerm.toGraph (number 1) 20 = observed at related ⊢
  cases related with
  | linked exports =>
    exact ⟨_, rfl, matchingGlobal 0 8 (exports.get .head), matchingGlobal 1 9 (exports.get (.tail .head))⟩

private abbrev fn : Function Unit Unit := ⟨[num, .control 2], [num]⟩
private abbrev bodyInput : Ports T := [global, fn.port, num, .control 2]

private abbrev effect {past : List (Ports T)} : NestedTheta.Node (Instruction Op) bodyInput past [num] :=
  ⟨[global, num], .base (.simple (.primitive .finish)),
    .cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil), fun i => i.elim0⟩

private abbrev emptyBranch {past : List (Ports T)} : NestedTheta.Node (Instruction Op) bodyInput past [] :=
  ⟨[.control 2], .base (.gamma (entry := []) (exit := []) 0),
    .cons (.arg (.tail (.tail (.tail .head)))) .nil, fun _ => []⟩

private abbrev callSelf {past : List (Ports T)} : NestedTheta.Node (Instruction Op) bodyInput past [num] :=
  ⟨fn.port :: fn.args, .base (.simple (.apply fn)),
    .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head)))
      (.cons (.arg (.tail (.tail (.tail .head)))) .nil)), fun i => i.elim0⟩

-- The caller retains the finish result across the recursive application.
-- The independent empty γ moves, but the effect still precedes the call.
private def memberBodyL : NestedTheta.Term (Instruction Op) bodyInput [] [[num], [], [num]] [num] :=
  .bind effect (fun i => i.elim0) <| .bind emptyBranch (fun _ => .ret .nil) <|
    .bind callSelf (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 3) .head) .nil))

private def memberBodyR : NestedTheta.Term (Instruction Op) bodyInput [] [[], [num], [num]] [num] :=
  .bind emptyBranch (fun _ => .ret .nil) <| .bind effect (fun i => i.elim0) <|
    .bind callSelf (fun i => i.elim0) (.ret (.cons (.output (1 : Fin 3) .head) .nil))

private def bodyPositions : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

private theorem memberBodyIso :
    NestedTheta.Graph.Isomorphic (Instruction Op) memberBodyL.toGraph memberBodyR.toGraph := by
  refine .intro rfl rfl bodyPositions ?_ ?_ rfl ?_
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  · refine Fin.cases (fun j => j.elim0) (Fin.cases ?_ (Fin.cases (fun j => j.elim0) (fun i => i.elim0)))
    intro arm
    exact .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0) rfl (fun i => i.elim0)

private def selfGroup (member : Function Unit Unit) {past sigs : List (Ports T)}
    (source : Origin args past global)
    (body : NestedTheta.Term (Instruction Op) ([global, member.port] ++ member.args) [] sigs member.results) :
    PhiTerm Op args past [member] :=
  ⟨[global], .cons source .nil,
    .cons ⟨[global, member.port], .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), sigs, body⟩ .nil⟩

private def groupL := selfGroup fn (.output (0 : Fin 1) .head : Origin args [[global]] global) memberBodyL
private def groupR := selfGroup fn (.output (1 : Fin 2) .head : Origin args [[], [global]] global) memberBodyR

private def recursiveL : OmegaTerm Op args [fn.port] [[global], [fn.port], []] :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.phi groupL) <| .bind (.phi (emptyPhi Op args _)) <|
    .ret (.cons (.output (1 : Fin 3) .head) .nil)⟩

private def recursiveR : OmegaTerm Op args [fn.port] [[], [global], [fn.port]] :=
  ⟨.bind (.phi (emptyPhi Op args [])) <| .bind (.delta (seedDelta [[]])) <| .bind (.phi groupR) <|
    .ret (.cons (.output (2 : Fin 3) .head) .nil)⟩

private theorem groupsIso : groupL.Renumbered (renameVertex positions) groupR :=
  ⟨⟨rfl, rfl⟩, Fin.cases ⟨⟨rfl, rfl⟩, memberBodyIso⟩ (fun i => i.elim0)⟩

private theorem recursiveIso : recursiveL.toGraph.RenumberedBy recursiveR.toGraph positions :=
  (recursiveL.renumberedBy_toGraph_iff recursiveR positions).2
    ⟨Fin.cases (.delta ⟨⟨rfl, rfl⟩, noChildren_refl _ (fun i => Fin.cases rfl (fun j => j.elim0) i)⟩)
      (Fin.cases (.phi groupsIso) (Fin.cases (.phi ⟨⟨rfl, rfl⟩, fun i => i.elim0⟩) (fun i => i.elim0))), rfl⟩

private theorem recursiveOrder : Ordered Op (renameVertex positions) args [fn.port]
    recursiveL.toGraph.toTerm.region recursiveR.toGraph.toTerm.region := by
  rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
  exact .emptyRight (.bind rfl (.delta ⟨rfl, rfl⟩ seedTerm)
    (.bind rfl (.phi groupsIso) (.emptyLeft (.ret _ _))))

private def refL : machine.Val fn.port :=
  .member (.cons (globalValue 0 8) .nil) groupL.toGraph.definitions 0

private def refR : machine.Val fn.port :=
  .member (.cons (globalValue 1 8) .nil) groupR.toGraph.definitions 0

private theorem recursiveLinksL :
    link primitives 73 recursiveL.toGraph (number 1) 20 = .linked (.cons refL .nil) 23 :=
  (Executable.link_eq actions 73 recursiveL.toGraph (number 1) 20).symm.trans (by cbv)

private theorem recursiveLinksR :
    link primitives 73 recursiveR.toGraph (number 1) 20 = .linked (.cons refR .nil) 23 :=
  (Executable.link_eq actions 73 recursiveR.toGraph (number 1) 20).symm.trans (by cbv)

-- Slot zero sees its own linked reference and the relocated δ in capture order.
example : resolve machine refL =
    ⟨[global, fn.port], .cons (globalValue 0 8) (.cons refL .nil), _, memberBodyL.toGraph⟩ := rfl

example : resolve machine refR =
    ⟨[global, fn.port], .cons (globalValue 1 8) (.cons refR .nil), _, memberBodyR.toGraph⟩ := rfl

private theorem recursiveCallees : ValueRelated machine ids refL refR := by
  have imports : TupleRelated machine ids (number 1) (number 1) :=
    .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) (1 : Nat)) .nil
  have paired := link_related (unitL := 73) (unitR := 73) respects recursiveIso recursiveOrder
    (fun _ => ⟨rfl, rfl⟩) imports 20
  rw [recursiveLinksL, recursiveLinksR] at paired
  cases paired with
  | linked exports => exact exports.get .head

example : TupleRelated machine ids (resolve machine refL).values (resolve machine refR).values ∧
    NestedTheta.Graph.Isomorphic (Instruction Op) (resolve machine refL).body (resolve machine refR).body :=
  resolve_related recursiveCallees

private def recursiveArgs : Tuple machine.Val fn.args := .cons (.data (1 : Nat)) (.cons (.control 0) .nil)

private def recursivePrefix {sigs : List (Ports T)} (graph : Omega Op args [fn.port] sigs) :
    Option (Config machine Nat [num]) :=
  (Executable.start actions 73 graph (number 1) .head recursiveArgs 20).toOption.map (runFor actions 20)

open RecursiveCall (Schedule ResolvedSchedule Frames Live Advance DispatchReady)
open Continuation (Stack)

private def memberVertices : Nat ≃ Nat := Equiv.swap 0 1

private theorem memberSchedule :
    Schedule Op memberVertices memberBodyL memberBodyR :=
  .emptyRight _ (.bind (.primitive Op.finish) _ _ rfl rfl
    (.emptyLeft _ (.bind (.apply fn) _ _ rfl rfl (.ret _ _ rfl))))

private theorem selectedSchedule : ResolvedSchedule Op machine fn (resolve machine refL) (resolve machine refR) := by
  apply ResolvedSchedule.intro (vertices := memberVertices)
  change Schedule Op memberVertices memberBodyL.toGraph.toTerm memberBodyR.toGraph.toTerm
  simpa only [NestedTheta.Term.toTerm_toGraph] using memberSchedule

private theorem relatedArgs : TupleRelated machine ids recursiveArgs recursiveArgs :=
  .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) (1 : Nat)) (.cons (.control 0) .nil)

private def entryOf (vertex : Nat) (ref : machine.Val fn.port) : Tuple machine.Val bodyInput :=
  .cons (globalValue vertex 8) (.cons ref recursiveArgs)

private def storedL : Locals machine.Val [[num], []] := (number 9, .nil, PUnit.unit)
private def storedR : Locals machine.Val [[], [num]] := (.nil, number 9, PUnit.unit)

private def savedL (outer : Stack machine [num] [num]) : Stack machine [num] [num] :=
  .resume (past := [[num], []]) (.ret (.cons (.output (0 : Fin 3) .head) .nil)) (entryOf 0 refL) storedL outer

private def savedR (outer : Stack machine [num] [num]) : Stack machine [num] [num] :=
  .resume (past := [[], [num]]) (.ret (.cons (.output (1 : Fin 3) .head) .nil)) (entryOf 1 refR) storedR outer

private theorem savedPair {left right : Stack machine [num] [num]} (outer : Frames machine ids [num] left right) :
    Frames machine ids [num] (savedL left) (savedR right) := by
  have entry : TupleRelated machine ids (entryOf 0 refL) (entryOf 1 refR) :=
    .cons (.global ⟨rfl, rfl⟩ (ValueRelated.data (m := machine) (ids := ids) (t := ()) (8 : Nat)))
      (.cons recursiveCallees relatedArgs)
  have outputs : TupleRelated machine ids (number 9) (number 9) :=
    .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) (9 : Nat)) .nil
  have locals : LocalsRelated machine ids memberVertices storedL storedR :=
    ((LocalsRelated.empty (m := machine) (ids := ids) (rename := memberVertices)).emptyRight.snoc
      memberVertices.injective rfl outputs).emptyLeft
  exact .resume (vertices := memberVertices) rfl (.ret _ _ rfl) entry locals outer

private def checkpointL : Config machine Nat [num] :=
  ⟨.eval (.call refL recursiveArgs) (savedL (savedL .halt)), 33⟩

private def checkpointR : Config machine Nat [num] :=
  ⟨.eval (.call refR recursiveArgs) (savedR (savedR .halt)), 33⟩

private theorem reachedL : recursivePrefix recursiveL.toGraph = some checkpointL := by cbv
private theorem reachedR : recursivePrefix recursiveR.toGraph = some checkpointR := by cbv

private def enteredL : Config machine Nat [num] :=
  ⟨.eval (Job.openClosure machine refL recursiveArgs) (savedL (savedL .halt)), 33⟩

private def enteredR : Config machine Nat [num] :=
  ⟨.eval (Job.openClosure machine refR recursiveArgs) (savedR (savedR .halt)), 33⟩

private theorem enteredPair : Live machine ids Nat [num] enteredL enteredR :=
  RecursiveCall.open_related recursiveCallees relatedArgs selectedSchedule (savedPair (savedPair .halt)) 33

-- Dispatch from the real runner checkpoints. Both saved suffixes stay live.
example : recursivePrefix recursiveL.toGraph = some checkpointL ∧
    recursivePrefix recursiveR.toGraph = some checkpointR ∧
    Continuation.Partial.Step primitives checkpointL enteredL ∧
    Continuation.Partial.Step primitives checkpointR enteredR ∧
    Live machine ids Nat [num] enteredL enteredR :=
  ⟨reachedL, reachedR, Continuation.Partial.Step.of_next_some rfl,
    Continuation.Partial.Step.of_next_some rfl, enteredPair⟩

-- On repeated entry, the right machine passes a γ before reaching the
-- aligned primitive, while the left machine reaches it in one microstep.
example : Advance primitives ids enteredL enteredR := by
  apply RecursiveCall.advance respects enteredPair
  intro _ _ _ _ _ _ _ _ left _
  cases left

example : Advance primitives ids checkpointL checkpointR :=
  RecursiveCall.advance respects (.call 33 recursiveCallees relatedArgs (savedPair (savedPair .halt)))
    (DispatchReady.call selectedSchedule)

private def finishOperands {ins outs : Ports T} (opcode : Op ins outs)
    (input : Tuple machine.Val ins) : Option (Nat × Nat) :=
  match opcode with
  | .seed => none
  | .finish =>
    let .global _ source _ := input.get .head
    let .data flag := input.get (.tail .head)
    some (source, flag)

private def soleFrameVertex {ports : Ports T} : Stack machine ports [num] → Option Nat
  | .resume (past := past) _ _ _ .halt => some past.length
  | _ => none

private def blockedAttempt :
    Continuation.Partial.Executable.Observation machine Nat [num] → Option (Nat × Nat × Nat × Nat)
  | .blocked active store => do
    let vertex ← soleFrameVertex active.stack
    let (source, flag) ← finishOperands active.site.opcode active.site.input
    some (vertex, source, flag, store)
  | _ => none

private def selectedBlock {sigs : List (Ports T)} (graph : Omega Op args [fn.port] sigs) :
    Option (Nat × Nat × Nat × Nat) :=
  let callArgs : Tuple machine.Val fn.args := .cons (.data (0 : Nat)) (.cons (.control 0) .nil)
  (Executable.run actions 10 73 graph (number 1) .head callArgs 20).toOption.bind blockedAttempt

-- The selected undefined primitive has its own pending suffix. Its
-- address and captured global relocate, with the same flag and store.
example : selectedBlock recursiveL.toGraph = some (0, 0, 0, 23) := by cbv
example : selectedBlock recursiveR.toGraph = some (1, 1, 0, 23) := by cbv

open RecursiveCall (Family TupleIn Closed ClosedFamily Admitted)
open Continuation.Partial (Step)
open Relation (ReflTransGen TransGen)

-- One actual member is the only admissible callable on each side. The
-- family includes arbitrary ordinary data, controls and captured globals.
private inductive Supported {fn : Function Unit Unit} (member : machine.Val fn.port) : Family machine where
  | number (n : Nat) : Supported member (.data (t := ()) n)
  | capture (unit vertex n : Nat) : Supported member (.global unit vertex (.data (t := ()) n))
  | control {n : Nat} (tag : Fin n) : Supported member (.control tag)
  | self : Supported member member

private theorem numberIn {fn : Function Unit Unit} {member : machine.Val fn.port} (output : Tuple machine.Val [num]) :
    TupleIn (Supported member) output := by
  cases output with
  | cons value tail =>
    cases value with
    | data n =>
      cases tail
      exact ⟨.number n, trivial⟩

private theorem primitivesClosed {fn : Function Unit Unit} (member : machine.Val fn.port)
    (captures : ∀ {args outs : Ports T} {ref : machine.Val (.value (.function args outs))},
      Supported member ref → TupleIn (Supported member) (resolve machine ref).values) :
    Closed primitives (Supported member) where
  captures := captures
  primitive := by
    intro _ _ opcode _ _ _ _ output _
    cases opcode <;> exact numberIn output

private theorem supportedFamily : ClosedFamily primitives ids (Supported refL) (Supported refR) where
  closedL := primitivesClosed refL (by
    intro _ _ _ member
    cases member
    exact ⟨.capture 73 0 8, .self, trivial⟩)
  closedR := primitivesClosed refR (by
    intro _ _ _ member
    cases member
    exact ⟨.capture 73 1 8, .self, trivial⟩)
  schedule := by
    intro _ _ _ _ left right _
    cases left
    cases right
    exact selectedSchedule

private def invocation (ref : machine.Val fn.port) (stack : Stack machine [num] [num])
    (store : Nat) : Config machine Nat [num] :=
  ⟨.eval (.call ref recursiveArgs) stack, store⟩

private theorem callSegment (stack : Stack machine [num] [num]) (store : Nat) :
    TransGen (Step primitives) (invocation refL stack store) (invocation refL (savedL stack) (store + 5)) := by
  let entry : Config machine Nat [num] := ⟨.eval (Job.openClosure machine refL recursiveArgs) stack, store⟩
  have entered : Step primitives (invocation refL stack store) entry := Step.of_next_some rfl
  have more := Continuation.Partial.Executable.runFor_reachable actions 9 entry
  have checkpoint : runFor actions 9 entry = invocation refL (savedL stack) (store + 5) := by cbv
  exact TransGen.head' entered (checkpoint ▸ more)

private theorem productiveLeft : InfiniteTrace (Step primitives) (invocation refL .halt 23) := by
  apply InfiniteTrace.coinduct (fun cfg =>
    ∃ stack store, ReflTransGen (Step primitives) cfg (invocation refL stack store)) ?_ ⟨.halt, 23, .refl⟩
  rintro cfg ⟨stack, store, path⟩
  obtain ⟨next, picked, rest⟩ := TransGen.head'_iff.mp (TransGen.trans_right path (callSegment stack store))
  exact ⟨next, picked, savedL stack, store + 5, rest⟩

private theorem admittedExports :
    Admitted machine ids (Supported refL) (Supported refR) (invocation refL .halt 23) (invocation refR .halt 23) :=
  Admitted.call recursiveCallees relatedArgs .self .self
    ⟨.number 1, .control 0, trivial⟩ ⟨.number 1, .control 0, trivial⟩ 23

-- These are actual starts from the linked export. Every recursive
-- activation adds a pending non-tail frame and changes the store by five.
example : ∃ sourceL sourceR,
    Executable.start actions 73 recursiveL.toGraph (number 1) .head recursiveArgs 20 = .ok sourceL ∧
    Executable.start actions 73 recursiveR.toGraph (number 1) .head recursiveArgs 20 = .ok sourceR ∧
    InfiniteTrace (Step primitives) sourceL ∧ InfiniteTrace (Step primitives) sourceR := by
  refine ⟨invocation refL .halt 23, invocation refR .halt 23, ?_, ?_, productiveLeft, ?_⟩
  · cbv
  · cbv
  · exact (ClosedFamily.infinite_iff respects supportedFamily admittedExports).mp productiveLeft

private def blockedArgs : Tuple machine.Val fn.args := .cons (.data (0 : Nat)) (.cons (.control 0) .nil)

private def blockingEntry (ref : machine.Val fn.port) : Config machine Nat [num] :=
  ⟨Continuation.start (.call ref blockedArgs), 23⟩

private theorem relatedBlockedArgs : TupleRelated machine ids blockedArgs blockedArgs :=
  .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) (0 : Nat)) (.cons (.control 0) .nil)

private theorem admittedBlocking :
    Admitted machine ids (Supported refL) (Supported refR) (blockingEntry refL) (blockingEntry refR) :=
  Admitted.call recursiveCallees relatedBlockedArgs .self .self
    ⟨.number 0, .control 0, trivial⟩ ⟨.number 0, .control 0, trivial⟩ 23

-- Reflect the actual left runner endpoint into a matched pair of
-- terminal configurations, including the precise right blocked attempt.
example : ∃ endR,
    RecursiveCall.ReachedTerminal primitives ids (blockingEntry refL) (blockingEntry refR)
      (runFor actions 10 (blockingEntry refL)) endR ∧ endR.Blocked primitives := by
  apply (ClosedFamily.blocks respects supportedFamily admittedBlocking).1
  · exact Continuation.Partial.Executable.runFor_reachable actions 10 (blockingEntry refL)
  · exact ⟨_, by cbv, by cbv⟩

private abbrev control : T := .control 2
private abbrev branchFn : Function Unit Unit := ⟨[num, control, control], [num]⟩
private abbrev captured : Ports T := [global, branchFn.port, num, control]
private abbrev branchEntry : Ports T := [global, branchFn.port, num, control, control]

private abbrev finishNode {past : List (Ports T)} : NestedTheta.Node (Instruction Op) captured past [num] :=
  RecursiveCall.simple (.primitive Op.finish)
    (.cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil)) (fun i => i.elim0)

private abbrev inertNode {past : List (Ports T)} : NestedTheta.Node (Instruction Op) captured past [] :=
  RecursiveCall.emptyGamma (extra := 0) (entry := [])
    (.cons (.arg (.tail (.tail (.tail .head)))) .nil)

-- Only the administrative binding moves. The primitive that reads the
-- captured global is at vertex 0 on the left and vertex 1 on the right.
private def baseL : RecursiveCall.Code Op captured [] [[num], []] [num] :=
  .bind finishNode (fun i => i.elim0) <| .bind inertNode (fun _ => .ret .nil) <|
    .ret (.cons (.output (0 : Fin 2) .head) .nil)

private def baseR : RecursiveCall.Code Op captured [] [[], [num]] [num] :=
  .bind inertNode (fun _ => .ret .nil) <| .bind finishNode (fun i => i.elim0) <|
    .ret (.cons (.output (1 : Fin 2) .head) .nil)

private def addAfter {entry : Ports T} : RecursiveCall.Code Op entry [[num]] [[num]] [num] :=
  .bind (RecursiveCall.simple (.primitive Op.seed) (.cons (.output (0 : Fin 1) .head) .nil) (fun i => i.elim0))
    (fun i => i.elim0) (.ret (.cons (.output (1 : Fin 2) .head) .nil))

-- Pass the carried exit selector to the recursive call, then use its
-- returned tuple in a state-changing suffix.
private def recurArm : RecursiveCall.Code Op captured [] [[num], [num]] [num] :=
  let after := Origin.arg (.tail (.tail (.tail .head))) (past := [])
  .bind (RecursiveCall.simple (.apply branchFn)
    (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) (.cons after (.cons after .nil))))
    (fun i => i.elim0)) (fun i => i.elim0) addAfter

private def branchWires : Wires branchEntry [] (control :: captured) :=
  .cons (.arg (.tail (.tail (.tail .head))))
    (.cons (.arg .head) (.cons (.arg (.tail .head))
      (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil))))

private def branchSigs (sigs : List (Ports T)) : Fin 2 → List (Ports T) :=
  Fin.cases sigs fun _ => [[num], [num]]

private def branchChildren {sigs : List (Ports T)} (base : RecursiveCall.Code Op captured [] sigs [num])
    (tag : Fin 2) : RecursiveCall.Code Op captured [] (branchSigs sigs tag) [num] :=
  Fin.cases (n := 1) (motive := fun i => RecursiveCall.Code Op captured [] (branchSigs sigs i) [num])
    base (fun _ => recurArm) tag

private def branchBody {sigs : List (Ports T)} (base : RecursiveCall.Code Op captured [] sigs [num]) :
    RecursiveCall.Code Op branchEntry [] [[num], [num]] [num] :=
  .bind (RecursiveCall.gammaNode (extra := 0) (entry := captured) (outs := [num])
    branchWires (branchSigs sigs)) (branchChildren base) addAfter

local instance : DecidableEq (Ty Unit Unit) := RecursiveCall.Numbered.decidePort

private def opcodeCode : NestedTheta.Equality.OpcodeCode Op where
  Key := Nat
  encode
    | .seed => 0
    | .finish => 1
  injective := by intro _ _ x y _; cases x <;> cases y <;> rfl

private abbrev instructionKeys := RecursiveCall.Numbered.instructionCode opcodeCode

private instance : DecidableEq instructionKeys.Key :=
  show DecidableEq (Sum Nat (Ports T × Ports T)) from inferInstance

private theorem baseIso : NestedTheta.Graph.Isomorphic (Instruction Op) baseL.toGraph baseR.toGraph := by
  refine .intro rfl rfl (Equiv.swap (0 : Fin 2) 1) ?_ ?_ rfl ?_
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · refine Fin.cases (fun i => i.elim0) (Fin.cases ?_ (fun i => i.elim0))
    intro arm
    exact NestedTheta.Graph.Isomorphic.refl _

private theorem branchBodyIso :
    NestedTheta.Graph.Isomorphic (Instruction Op) (branchBody baseL).toGraph (branchBody baseR).toGraph := by
  refine .intro rfl rfl (Equiv.refl _) ?_ ?_ rfl ?_
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · exact Fin.cases (Fin.cases baseIso (Fin.cases (NestedTheta.Graph.Isomorphic.refl _) (fun i => i.elim0)))
      (Fin.cases (fun i => i.elim0) (fun i => i.elim0))

private def branchGroupL := selfGroup branchFn (.output (0 : Fin 1) .head : Origin args [[global]] global)
  (branchBody baseL)
private def branchGroupR := selfGroup branchFn (.output (1 : Fin 2) .head : Origin args [[], [global]] global)
  (branchBody baseR)

private def branchModuleL : OmegaTerm Op args [branchFn.port] [[global], [branchFn.port], []] :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.phi branchGroupL) <| .bind (.phi (emptyPhi Op args _)) <|
    .ret (.cons (.output (1 : Fin 3) .head) .nil)⟩

private def branchModuleR : OmegaTerm Op args [branchFn.port] [[], [global], [branchFn.port]] :=
  ⟨.bind (.phi (emptyPhi Op args [])) <| .bind (.delta (seedDelta [[]])) <| .bind (.phi branchGroupR) <|
    .ret (.cons (.output (2 : Fin 3) .head) .nil)⟩

private def branchRefL : machine.Val branchFn.port :=
  .member (.cons (globalValue 0 8) .nil) branchGroupL.toGraph.definitions 0

private def branchRefR : machine.Val branchFn.port :=
  .member (.cons (globalValue 1 8) .nil) branchGroupR.toGraph.definitions 0

private theorem branchRefs : ValueRelated machine ids branchRefL branchRefR := by
  have capture : ValueRelated machine ids (globalValue 0 8) (globalValue 1 8) :=
    .global ⟨rfl, rfl⟩ (ValueRelated.data (m := machine) (ids := ids) (t := ()) (8 : Nat))
  refine .member (members := [branchFn]) (tableL := branchGroupL.toGraph.definitions)
    (tableR := branchGroupR.toGraph.definitions) (.cons capture .nil) ?_ 0
  exact Fin.cases ⟨⟨rfl, rfl⟩, branchBodyIso⟩ (fun i => i.elim0)

private theorem checkedBranchFamily :
    RecursiveCall.Numbered.CheckedFamily primitives ids (Supported branchRefL) (Supported branchRefR) where
  closedL := primitivesClosed branchRefL (by
    intro _ _ _ member
    cases member
    exact ⟨.capture 73 0 8, .self, trivial⟩)
  closedR := primitivesClosed branchRefR (by
    intro _ _ _ member
    cases member
    exact ⟨.capture 73 1 8, .self, trivial⟩)
  graphs := by
    intro _ _ _ _ left right _
    cases left
    cases right
    exact RecursiveCall.Numbered.inferResolved_sound (keys := instructionKeys) (by cbv)

private theorem branchFamily : ClosedFamily primitives ids (Supported branchRefL) (Supported branchRefR) :=
  checkedBranchFamily.toClosed

private def branchArgs (flag : Nat) : Tuple machine.Val branchFn.args :=
  .cons (.data flag) (.cons (.control 1) (.cons (.control 0) .nil))

private def branchStart (ref : machine.Val branchFn.port) (flag : Nat) : Config machine Nat [num] :=
  ⟨Continuation.start (.call ref (branchArgs flag)), 23⟩

private theorem branchAdmitted (flag : Nat) :
    Admitted machine ids (Supported branchRefL) (Supported branchRefR)
      (branchStart branchRefL flag) (branchStart branchRefR flag) := by
  have inputs : TupleRelated machine ids (branchArgs flag) (branchArgs flag) :=
    .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) flag)
      (.cons (.control 1) (.cons (.control 0) .nil))
  exact Admitted.call (familyL := Supported branchRefL) (familyR := Supported branchRefR)
    branchRefs inputs .self .self ⟨.number flag, .control 1, .control 0, trivial⟩
    ⟨.number flag, .control 1, .control 0, trivial⟩ 23

private theorem branchLinkedL (flag : Nat) :
    Executable.start actions 73 branchModuleL.toGraph (number 1) .head (branchArgs flag) 20 =
      .ok (branchStart branchRefL flag) := by cbv

private theorem branchLinkedR (flag : Nat) :
    Executable.start actions 73 branchModuleR.toGraph (number 1) .head (branchArgs flag) 20 =
      .ok (branchStart branchRefR flag) := by cbv

-- Arm 1 recurses into arm 0. After the primitive, all three suffixes run
-- (the child join, the recursive arm, and the outer join).
example : Executable.run actions 40 73 branchModuleL.toGraph (number 1) .head (branchArgs 1) 20 =
    .ok (.returned (number 30) 37) := by cbv

example : ∃ sourceL sourceR endR,
    Executable.start actions 73 branchModuleL.toGraph (number 1) .head (branchArgs 1) 20 = .ok sourceL ∧
    Executable.start actions 73 branchModuleR.toGraph (number 1) .head (branchArgs 1) 20 = .ok sourceR ∧
    ReflTransGen (Step primitives) sourceR endR ∧ endR.result = some (number 30, 37) := by
  have reached := Continuation.Partial.Executable.runFor_reachable actions 40 (branchStart branchRefL 1)
  have result : (runFor actions 40 (branchStart branchRefL 1)).result = some (number 30, 37) := by cbv
  obtain ⟨endR, valueR, path, got, values⟩ :=
    (ClosedFamily.returns respects branchFamily (branchAdmitted 1)).1 _ _ _ reached result
  cases values with
  | cons paired tail =>
    cases paired
    cases tail
    exact ⟨_, _, endR, branchLinkedL 1, branchLinkedR 1, path, got⟩

private def savedVertices {ports results : Ports T} : Stack machine ports results → List Nat
  | .halt => []
  | .resume (past := past) _ _ _ outer => past.length :: savedVertices outer
  | .loop _ outer => savedVertices outer

private def branchAttempt :
    Continuation.Partial.Executable.Observation machine Nat [num] → Option (List Nat × Nat × Nat × Nat)
  | .blocked active store => do
    let (source, flag) ← finishOperands active.site.opcode active.site.input
    some (savedVertices active.stack, source, flag, store)
  | _ => none

-- At the undefined attempt the primitive, both γ joins and the recursive
-- application still have their actual frames. Only the inner site moves.
example : (Executable.run actions 40 73 branchModuleL.toGraph (number 1) .head (branchArgs 0) 20
    |>.toOption.bind branchAttempt) = some ([0, 0, 0, 0], 0, 0, 23) := by cbv

example : (Executable.run actions 40 73 branchModuleR.toGraph (number 1) .head (branchArgs 0) 20
    |>.toOption.bind branchAttempt) = some ([1, 0, 0, 0], 1, 0, 23) := by cbv

example : ∃ sourceL sourceR endR,
    Executable.start actions 73 branchModuleL.toGraph (number 1) .head (branchArgs 0) 20 = .ok sourceL ∧
    Executable.start actions 73 branchModuleR.toGraph (number 1) .head (branchArgs 0) 20 = .ok sourceR ∧
    RecursiveCall.ReachedTerminal primitives ids sourceL sourceR (runFor actions 40 sourceL) endR ∧
    endR.Blocked primitives := by
  obtain ⟨endR, pair, blocked⟩ := (ClosedFamily.blocks respects branchFamily (branchAdmitted 0)).1 _
    (Continuation.Partial.Executable.runFor_reachable actions 40 (branchStart branchRefL 0))
    ⟨_, by cbv, by cbv⟩
  exact ⟨_, _, endR, branchLinkedL 0, branchLinkedR 0, pair, blocked⟩

private abbrev seedRow {past : List (Ports T)} : NestedTheta.Node (Instruction Op) [global, num] past [num] :=
  RecursiveCall.simple (.primitive Op.seed) (.cons (.arg (.tail .head)) .nil) (fun i => i.elim0)

private abbrev finishRow {past : List (Ports T)} : NestedTheta.Node (Instruction Op) [global, num] past [num] :=
  RecursiveCall.simple (.primitive Op.finish)
    (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) (fun i => i.elim0)

private def seedThenFinish : RecursiveCall.Code Op [global, num] [] [[num], [num]] [] :=
  .bind seedRow (fun i => i.elim0) (.bind finishRow (fun i => i.elim0) (.ret .nil))

private def finishThenSeed : RecursiveCall.Code Op [global, num] [] [[num], [num]] [] :=
  .bind finishRow (fun i => i.elim0) (.bind seedRow (fun i => i.elim0) (.ret .nil))

-- The graph swap preserves both labels and their independent operands.
-- It moves the state change across a potentially undefined action.
example : NestedTheta.Graph.Isomorphic (Instruction Op) seedThenFinish.toGraph finishThenSeed.toGraph := by
  refine .intro rfl rfl (Equiv.swap (0 : Fin 2) 1) ?_ ?_ rfl ?_
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · exact Fin.cases (fun i => i.elim0) (Fin.cases (fun i => i.elim0) (fun i => i.elim0))

example : (RecursiveCall.Numbered.infer instructionKeys
    seedThenFinish.toGraph finishThenSeed.toGraph).isSome = false := by cbv

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Tests
