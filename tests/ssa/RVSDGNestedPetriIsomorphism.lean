module

import Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Tests

private abbrev Ty := PortType Unit Unit
private abbrev st : Ports Ty := [.state ()]
private abbrev val : Ports Ty := [.value ()]
private abbrev tickOut : Ports Ty := Theta.BodyResults st
private abbrev args : Ports Ty := .control 2 :: st
private abbrev outs : Ports Ty := st ++ val

private inductive Op : Ports Ty → Ports Ty → Type where
  | tick (canStop : Bool) : Op st tickOut
  | literal : Op [] val

private def model : Model Op where
  value _ := Nat
  state _ := Nat
  run
    | .tick canStop, .cons x .nil =>
      let y := (show Nat from x) + 1
      .cons (⟨if canStop && decide (2 ≤ y) then (0 : Fin 2) else 1⟩ : ULift (Fin 2))
        (.cons y .nil)
    | .literal, .nil => .cons (9 : Nat) .nil

private def state (n : Nat) : Tuple model.Val st := .cons n .nil
private def note : Tuple model.Val val := .cons (9 : Nat) .nil
private def input : Tuple model.Val args := .cons ⟨(1 : Fin 2)⟩ (state 0)
private def output : Tuple model.Val outs := .cons (2 : Nat) note

private abbrev tick {past : List (Ports Ty)} (canStop : Bool) : Node Op st past tickOut :=
  ⟨st, .base (.simple (.tick canStop)), .cons (.arg .head) .nil, fun i => i.elim0⟩

private abbrev literal {args : Ports Ty} {past : List (Ports Ty)} : Node Op args past val :=
  ⟨[], .base (.simple .literal), .nil, fun i => i.elim0⟩

private def bodyL (canStop : Bool) : Term Op st [] [tickOut, val] tickOut :=
  .bind (tick canStop) (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
    .bind literal (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
      .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (0 : Fin 2) (.tail .head)) .nil))

private def bodyR (canStop : Bool) : Term Op st [] [val, tickOut] tickOut :=
  .bind literal (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
    .bind (tick canStop) (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
      .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))

private def armL (arm : Fin 2) : Term Op st [] [st] st :=
  .bind (thetaVertex [tickOut, val]) (fun _ => bodyL (arm.val == 1)) (.ret (thetaResults st))

private def armR (arm : Fin 2) : Term Op st [] [st] st :=
  .bind (thetaVertex [val, tickOut]) (fun _ => bodyR (arm.val == 1)) (.ret (thetaResults st))

private abbrev selectNode {past : List (Ports Ty)} : Node Op args past st :=
  ⟨args, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), fun _ => [st]⟩

private def leftTerm : Term Op args [] [st, val] outs :=
  .bind selectNode armL <|
    .bind literal (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
      .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))

private def rightTerm : Term Op args [] [val, st] outs :=
  .bind literal (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
    .bind selectNode armR <|
      .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil))

private def left := leftTerm.toGraph
private def right := rightTerm.toGraph

private def exchange : Fin 2 → Fin 2 := Fin.cases 1 (Fin.cases 0 fun i => i.elim0)
private theorem exchange_twice (i : Fin 2) : exchange (exchange i) = i :=
  Fin.cases rfl (Fin.cases rfl fun j => j.elim0) i
private def swap : Fin 2 ≃ Fin 2 := ⟨exchange, exchange, exchange_twice, exchange_twice⟩

private def bodyMap (canStop : Bool) : Renumbering Op (bodyL canStop).toGraph (bodyR canStop).toGraph := by
  refine .intro rfl rfl swap ?_ ?_ rfl ?_
  · exact fun i => Fin.cases rfl (Fin.cases rfl fun j => j.elim0) i
  · exact fun i => Fin.cases rfl (Fin.cases rfl fun j => j.elim0) i
  · exact fun i => Fin.cases (fun j => j.elim0) (Fin.cases (fun j => j.elim0) fun j => j.elim0) i

private def armMap (arm : Fin 2) : Renumbering Op (armL arm).toGraph (armR arm).toGraph := by
  refine .intro rfl rfl (Equiv.refl _) ?_ ?_ rfl ?_
  · exact fun i => Fin.cases rfl (fun j => j.elim0) i
  · exact fun i => Fin.cases rfl (fun j => j.elim0) i
  · exact fun i => Fin.cases (fun _ => bodyMap (arm.val == 1)) (fun j => j.elim0) i

private def numbering : Renumbering Op left right := by
  refine .intro rfl rfl swap ?_ ?_ rfl ?_
  · exact fun i => Fin.cases rfl (Fin.cases rfl fun j => j.elim0) i
  · exact fun i => Fin.cases rfl (Fin.cases rfl fun j => j.elim0) i
  · exact fun i => Fin.cases armMap (Fin.cases (fun j => j.elim0) fun j => j.elim0) i

private abbrev MarkL := GraphMarking model left
private abbrev MarkR := GraphMarking model right
private abbrev chosenL := left.children (0 : Fin 2) ⟨1, by decide⟩
private abbrev chosenR := right.children (1 : Fin 2) ⟨1, by decide⟩
private abbrev BodyL := GraphMarking model (chosenL.children (0 : Fin 1) ⟨0, by decide⟩)
private abbrev BodyR := GraphMarking model (chosenR.children (0 : Fin 1) ⟨0, by decide⟩)

private def liveL (carried : Nat) (body : BodyL) (sibling : Bool) : MarkL :=
  (.waiting (1 : Fin 2) (state 0, .waiting (0 : Fin 1) (state carried, body), PUnit.unit),
    if sibling then .done note else .pending, PUnit.unit)

private def liveR (carried : Nat) (body : BodyR) : MarkR :=
  (.done note, .waiting (1 : Fin 2) (state 0, .waiting (0 : Fin 1) (state carried, body), PUnit.unit),
    PUnit.unit)

private def afterEntry : MarkL :=
  (.waiting (1 : Fin 2) (state 0, .pending, PUnit.unit), .pending, PUnit.unit)
private def emptyL : BodyL := (.pending, .pending, PUnit.unit)
private def emptyR : BodyR := (.pending, .pending, PUnit.unit)
private def continuing := Theta.bodyResult model true (state 1)
private def stopping := Theta.bodyResult model false (state 2)
private def beforeRestartL := liveL 0 (.done continuing, .done note, PUnit.unit) true
private def beforeRestartR := liveR 0 (.done note, .done continuing, PUnit.unit)
private def afterRestartL := liveL 1 emptyL true
private def afterRestartR := liveR 1 emptyR
private def completeL : MarkL := (.done (state 2), .done note, PUnit.unit)

-- The root sibling fires while γ and θ are active. In the second iteration,
-- the two body vertices fire in the opposite order from the first.
private theorem schedule : Steps (Step model left input) 10 (initial model left) completeL := by
  have a : Step model left input (initial model left) afterEntry := .enter rfl rfl
  have b : Step model left input afterEntry (liveL 0 emptyL false) := .advance (.enter rfl rfl)
  have c : Step model left input (liveL 0 emptyL false) (liveL 0 (.done continuing, .pending, PUnit.unit) false) :=
    .advance (.advance (.primitive rfl rfl))
  have d : Step model left input (liveL 0 (.done continuing, .pending, PUnit.unit) false)
      (liveL 0 (.done continuing, .pending, PUnit.unit) true) := .later (.primitive rfl rfl)
  have e : Step model left input (liveL 0 (.done continuing, .pending, PUnit.unit) true) beforeRestartL :=
    .advance (.advance (.later (.primitive rfl rfl)))
  have f : Step model left input beforeRestartL afterRestartL := .advance (.restart rfl rfl rfl)
  have g : Step model left input afterRestartL (liveL 1 (.pending, .done note, PUnit.unit) true) :=
    .advance (.advance (.later (.primitive rfl rfl)))
  have h : Step model left input (liveL 1 (.pending, .done note, PUnit.unit) true)
      (liveL 1 (.done stopping, .done note, PUnit.unit) true) := .advance (.advance (.primitive rfl rfl))
  have i : Step model left input (liveL 1 (.done stopping, .done note, PUnit.unit) true)
      (.waiting (1 : Fin 2) (state 0, .done (state 2), PUnit.unit), .done note, PUnit.unit) :=
    .advance (.commit rfl rfl)
  have j : Step model left input
      (.waiting (1 : Fin 2) (state 0, .done (state 2), PUnit.unit), .done note, PUnit.unit) completeL :=
    .commit rfl rfl
  exact ((((((((((Steps.refl _).tail a).tail b).tail c).tail d).tail e).tail f).tail g).tail h).tail i).tail j

set_option maxHeartbeats 500000 in
private theorem beforeRestartMatches : numbering.Matches model beforeRestartL beforeRestartR := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
  · refine ⟨rfl, rfl, ?_⟩
    intro j
    refine Fin.cases ?_ (fun k => k.elim0) j
    refine ⟨rfl, rfl, ?_⟩
    intro k
    refine Fin.cases ?_ (Fin.cases ?_ (fun l => l.elim0)) k
    · change continuing = continuing
      rfl
    · change note = note
      rfl
  · rfl

private theorem afterRestartMatches : numbering.Matches model afterRestartL afterRestartR := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
  · refine ⟨rfl, rfl, ?_⟩
    intro j
    refine Fin.cases ?_ (fun k => k.elim0) j
    refine ⟨rfl, rfl, ?_⟩
    intro k
    exact Fin.cases trivial (Fin.cases trivial (fun l => l.elim0)) k
  · rfl

-- The transported step has the concrete fresh right body and carries state 1.
example : Step model right input beforeRestartR afterRestartR :=
  (numbering.step_iff model input beforeRestartMatches afterRestartMatches).mp (.advance (.restart rfl rfl rfl))

example : ∃ target, PairedSteps (Step model left input) (Step model right input) (numbering.Matches model)
    10 (initial model left) (initial model right) completeL target ∧
    result model right input target = some output := by
  obtain ⟨target, paired⟩ := numbering.trace_forth model input (numbering.initial_matches model) schedule
  refine ⟨target, paired, ?_⟩
  cases paired with
  | tail _ _ _ current => exact (numbering.result_eq model input current).symm.trans rfl

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Tests
