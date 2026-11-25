module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Tests

open Continuation.Partial (Eval Primitives Site)
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

private def primitives : Primitives machine Nat where
  step
    | .seed, .cons (.data n) .nil => fun store => .some (number ((show Nat from n) + 7), store + 3)
    | .finish, .cons (.global _ _ (.data n)) (.cons (.data flag) .nil) => fun store =>
      let test : Nat := flag
      if test = 0 then .none else .some (number ((show Nat from n) + 1), store + 5)

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
                (if test = 0 then .none else .some (number ((show Nat from n) + 1), store + 5))
                (if test = 0 then .none else .some (number ((show Nat from n) + 1), store + 5))
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

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Tests
