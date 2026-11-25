module

import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Tests

private abbrev Ty := PortType Unit Unit
private abbrev carried : Ports Ty := [.state ()]
private abbrev resultPorts : Ports Ty := Theta.BodyResults carried
private abbrev args : Ports Ty := .control 2 :: carried

private inductive Op : Ports Ty → Ports Ty → Type where
  | tick (bound : Nat) : Op carried resultPorts
  | check (bound : Nat) : Op carried resultPorts

private def model : Model Op where
  value _ := Unit
  state _ := Nat
  run
    | .tick bound, .cons x .nil =>
      let y := (show Nat from x) + 1
      .cons (⟨if y < bound then (1 : Fin 2) else 0⟩ : ULift (Fin 2)) (.cons y .nil)
    | .check bound, .cons x .nil =>
      .cons (⟨if (show Nat from x) < bound then (1 : Fin 2) else 0⟩ : ULift (Fin 2)) (.cons x .nil)

private def state (n : Nat) : Tuple model.Val carried := .cons n .nil
private def inputs (tag : Fin 2) : Tuple model.Val args := .cons ⟨tag⟩ (state 0)

private def primitiveBody (op : Op carried resultPorts) : RVSDG.Term Op carried [] [resultPorts] resultPorts :=
  let node : RVSDG.Node Op carried [] resultPorts :=
    ⟨carried, .simple op, .cons (.arg .head) .nil, fun i => i.elim0⟩
  .bind node (fun i => Fin.elim0 (show Fin 0 from i))
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def baseBody (bound : Nat) := primitiveBody (.tick bound)

private def inner (bound : Nat) : Theta.Graph Op carried [resultPorts] :=
  ⟨(baseBody bound).toGraph⟩

-- One θ is inside another θ body. The inner θ increments once, and the enclosing
-- body's check decides whether to repeat the whole body.
private def outerBody : Term Op carried [] [carried, resultPorts] resultPorts :=
  let first : Node Op carried [] carried := thetaVertex [resultPorts]
  let check : Node Op carried [carried] resultPorts :=
    ⟨carried, .base (.simple (.check 4)), .cons (.output (0 : Fin 1) .head) .nil, fun i => i.elim0⟩
  .bind first (fun _ => Term.ofBase (baseBody 1)) <|
    .bind check (fun i => Fin.elim0 (show Fin 0 from i)) <|
      .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))

private abbrev gamma (firstSigs : List (Ports Ty)) : Node Op args [] carried :=
  ⟨args, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    Fin.cases firstSigs (fun _ => [carried])⟩

private abbrev afterGamma : Node Op args [carried] carried :=
  ⟨carried, .theta carried, .cons (.output (0 : Fin 1) .head) .nil, fun _ => [carried, resultPorts]⟩

private def table (firstSigs : List (Ports Ty)) : Nodes Op args [] [carried, carried] :=
  Fin.cases (gamma firstSigs) (Fin.cases afterGamma (fun i => i.elim0))

-- The graph is assembled directly. Its selected γ arm contains a θ, and the
-- following θ reads the γ result through an ordinary same-region wire.
private def rootWithArm {firstSigs : List (Ports Ty)} (first : Graph Op carried [] firstSigs carried) :
    Graph Op args [] [carried, carried] carried :=
  .region (table firstSigs)
    (Fin.cases
      (Fin.cases
        first
        (fun _ => Graph.ofTheta (inner 2)))
      (Fin.cases (fun _ => outerBody.toGraph) (fun i => i.elim0)))
    (.cons (.output (1 : Fin 2) .head) .nil)

private def root : Graph Op args [] [carried, carried] carried :=
  rootWithArm (firstSigs := []) (.region (fun i => i.elim0) (fun i => i.elim0) (.cons (.arg .head) .nil))

example : root.run model 1 (inputs 1) = none := rfl
example : root.run model 2 (inputs 1) = some (state 4) := rfl
example : root.run model 2 (inputs 0) = none := rfl
example : root.run model 4 (inputs 0) = some (state 4) := rfl

example : root.toTerm.Returns model (inputs 1) (state 4) :=
  (root.returns_iff model (inputs 1) (state 4)).1 ⟨2, rfl⟩

example : root.toTerm.toGraph = root := root.toGraph_toTerm

example : (Graph.ofTheta (inner 2)).Returns model (state 0) (state 2) :=
  ((Graph.returns_ofTheta (inner 2) model (state 0) (state 2))).2 (.again (next := state 1) rfl (.stop rfl))

-- Even though fuel 1 fails, the categorical result exists. The graph uses a θ
-- in the selected γ arm and a separate θ whose body itself contains a θ.
example : root.denotePart model (inputs 1) = Part.some (state 4) :=
  (root.denotePart_eq_some model (inputs 1) (state 4)).mpr ⟨2, rfl⟩

-- Choosing the other arm starts the outer θ earlier and needs four activations.
example : root.denotePart model (inputs 0) = Part.some (state 4) :=
  (root.denotePart_eq_some model (inputs 0) (state 4)).mpr ⟨4, rfl⟩

private def stalledBody : Graph Op carried [] [resultPorts] resultPorts :=
  Graph.ofBase (primitiveBody (.check 1)).toGraph

private def stalledArm : Graph Op carried [] [carried] carried :=
  Graph.ofTheta ⟨(primitiveBody (.check 1)).toGraph⟩

private def rootWithStalledArm : Graph Op args [] [carried, carried] carried :=
  rootWithArm stalledArm

example : rootWithStalledArm.denotePart model (inputs 1) = Part.some (state 4) :=
  (rootWithStalledArm.denotePart_eq_some model (inputs 1) (state 4)).mpr ⟨2, rfl⟩

private theorem stalled_iter (fuel : Nat) :
    iterate (stalledBody.run model fuel) (fun tag => tag.down.val == 1) fuel (state 0) = none := by
  have h : stalledBody.run model fuel (state 0) =
      some (Theta.bodyResult model true (state 0)) := rfl
  -- The body never consumes the iteration budget, so keep its evaluator fixed.
  suffices ∀ remaining,
      iterate (stalledBody.run model fuel) (fun tag => tag.down.val == 1) remaining (state 0) = none from
    this fuel
  intro remaining
  induction remaining with
  | zero => rfl
  | succ n ih =>
    rw [iterate, h]
    exact ih

private theorem stalled_arm_run (fuel : Nat) : stalledArm.run model fuel (state 0) = none := by
  change (iterate (stalledBody.run model fuel) (fun tag => tag.down.val == 1) fuel (state 0)).bind _ = none
  rw [stalled_iter fuel]
  rfl

private theorem stalled_run (fuel : Nat) : rootWithStalledArm.run model fuel (inputs 0) = none := by
  change (stalledArm.run model fuel (state 0)).bind _ = none
  rw [stalled_arm_run fuel]
  rfl

example : rootWithStalledArm.denotePart model (inputs 0) = Part.none := by
  apply (rootWithStalledArm.denotePart_eq_none model (inputs 0)).mpr
  intro output execution
  obtain ⟨fuel, run⟩ := (rootWithStalledArm.returns_iff model (inputs 0) output).mpr execution
  rw [stalled_run fuel] at run
  cases run

end Silmaril.SSA.RVSDG.NestedTheta.Tests
