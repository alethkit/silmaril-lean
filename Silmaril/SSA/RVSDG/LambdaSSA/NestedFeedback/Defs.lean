module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Defs

/-! # A flat two-header CFG with properly nested feedback -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback

open Isotope.LambdaSSA (Region)
open OrderedTheta (carried results carriedData resultData)
open OrderedRuntime.Structured
open TwoBlock (localTypes)
open TwoBlock.ExplicitRuntime.Skeleton (Closed)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K D : τ}

/-- Outer and inner headers accept independently typed payloads. Completing
the inner loop supplies the only input of the outer exit/feedback decision. -/
structure Loop (Φ : Type u) [HasTy Φ τ] (A B K D : τ) where
  enter : TwoBlock.Instruction Φ A B
  inner : TwoBlock.Instruction Φ B (Silmaril.coprod K B)
  finish : TwoBlock.Instruction Φ K (Silmaril.coprod D A)

def outerBlock (s : Loop Φ A B K D) : Region Φ :=
  .br 1 (.op s.enter.op (.var 0))

def innerBlock (s : Loop Φ A B K D) : Region Φ :=
  .case (.op s.inner.op (.var 0))
    (.case (.op s.finish.op (.var 0)) (.br 2 (.var 0)) (.br 0 (.var 0)))
    (.br 1 (.var 0))

def blocks (s : Loop Φ A B K D) : Fin 2 → Region Φ :=
  Fin.cases (outerBlock s) (fun _ => innerBlock s)

def region (s : Loop Φ A B K D) : Region Φ :=
  .cfg (.br 0 (.var 0)) 2 (blocks s)

theorem outerTyping (s : Loop Φ A B K D) : Region.HasType [A,A] (outerBlock s) [A,B,D] :=
  .br rfl (s.enter.typing [A])

theorem innerTyping (s : Loop Φ A B K D) : Region.HasType [B,A] (innerBlock s) [A,B,D] :=
  .case (s.inner.typing [A])
    (.case (s.finish.typing [B,A]) (.br rfl (.var rfl)) (.br rfl (.var rfl)))
    (.br rfl (.var rfl))

theorem blockTyping (s : Loop Φ A B K D) (i : Fin 2) :
    Region.HasType (localTypes A B i :: [A]) (blocks s i) [A,B,D] :=
  Fin.cases (motive := fun j => Region.HasType (localTypes A B j :: [A]) (blocks s j) [A,B,D])
    (outerTyping s) (fun _ => innerTyping s) i

theorem regionTyping (s : Loop Φ A B K D) : Region.HasType [A] (region s) [D] :=
  .cfg (localTypes A B) (.br rfl (.var rfl)) (blockTyping s)

abbrev Carrier (X Y : τ) : τ := Silmaril.coprod Y X

/-- These opcodes each apply one source instruction and encode its boundary
payload. The control structure is represented by the two θ vertices. -/
inductive Effect (Φ : Type u) [HasTy Φ τ] : Dialect.{u,u} τ PUnit where
  | enter {A B K D : τ} : TwoBlock.Instruction Φ A B →
      Effect Φ (carried (Carrier A D)) (carried (Carrier B K))
  | inner {B K : τ} : TwoBlock.Instruction Φ B (Carrier B K) →
      Effect Φ (carried (Carrier B K)) (results (Carrier B K))
  | finish {A B K D : τ} : TwoBlock.Instruction Φ K (Carrier A D) →
      Effect Φ (carried (Carrier B K)) (results (Carrier A D))

abbrev Pure (τ : Type u) : Dialect.{u,u} τ PUnit := fun _ _ => PEmpty
abbrev Op (Φ : Type u) [HasTy Φ τ] := Opcode (Pure τ) (Effect Φ)

namespace Wiring

open LinearChain.Wiring (newest)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

variable {args : Ports (OrderedRuntime.Structured.Ty τ)} {past : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {a : Data args}

def returnStep (Q : τ) :
    NestedTheta.ExplicitRuntime.Checked (Pure τ) (Effect Φ) a (resultData Q) (nextRuntime past (results Q))
      (.ret (withRuntime (nextRuntime past (results Q))
        (.cons (newest .head past) (.cons (newest (.tail .head) past) .nil)))) :=
  .ret _ _

def innerBody (op : TwoBlock.Instruction Φ B (Carrier B K)) :
    Closed (Pure τ) (Effect Φ) (carriedData (Carrier B K)) (resultData (Carrier B K))
      [Threaded (results (Carrier B K))] :=
  ⟨_, .primitive (.arg (runtimePort (carried (Carrier B K)))) (carriedData _) (resultData _)
    (.effect (.inner op)) (.cons (.arg .head) .nil) (returnStep _)⟩

abbrev BodySigs (A B K D : τ) : List (Ports (OrderedRuntime.Structured.Ty τ)) :=
  [Threaded (carried (Carrier B K)), Threaded (carried (Carrier B K)), Threaded (results (Carrier A D))]

/-- The inner θ gets the entry operation's token. Its returned payload and
token are the only operands of the final decision operation. -/
def outerBody (s : Loop Φ A B K D) :
    Closed (Pure τ) (Effect Φ) (carriedData (Carrier A D)) (resultData (Carrier A D))
      (BodySigs A B K D) :=
  let innerPorts := carried (Carrier B K)
  let enterSigs := [Threaded innerPorts]
  ⟨_, .primitive (.arg (runtimePort (carried (Carrier A D)))) (carriedData _) (carriedData _)
    (.effect (.enter s.enter)) (.cons (.arg .head) .nil)
    (.theta (nextRuntime [] innerPorts) (carriedData (Carrier B K))
      (.cons (newest .head []) .nil) [Threaded (results (Carrier B K))]
      (children := fun _ => (innerBody s.inner).1) (fun _ => (innerBody s.inner).2)
      (.primitive (nextRuntime enterSigs innerPorts) (carriedData _) (resultData _)
        (.effect (.finish s.finish)) (.cons (newest .head enterSigs) .nil) (returnStep _)))⟩

def loop (s : Loop Φ A B K D) :
    Closed (Pure τ) (Effect Φ) (carriedData (Carrier A D)) (carriedData (Carrier A D))
      [Threaded (carried (Carrier A D))] :=
  ⟨_, .theta (.arg (runtimePort (carried (Carrier A D)))) (carriedData _)
    (.cons (.arg .head) .nil) (BodySigs A B K D)
    (children := fun _ => (outerBody s).1) (fun _ => (outerBody s).2)
    (.ret (nextRuntime [] (carried (Carrier A D))) (.cons (newest .head []) .nil))⟩

end Wiring

abbrev Graph (Φ : Type u) [HasTy Φ τ] (A D : τ) :=
  TwoBlock.ExplicitRuntime.Skeleton.WireLoop (Pure τ) (Effect Φ) (Carrier A D)

def graph (s : Loop Φ A B K D) : Graph Φ A D := (Wiring.loop s).1.toGraph

def graphChecked (s : Loop Φ A B K D) :
    NestedTheta.ExplicitRuntime.EntryChecked (a := carriedData (Carrier A D))
      (b := carriedData (Carrier A D)) (graph s).toTerm :=
  (Wiring.loop s).2.collect

/-- A syntax-directed witness relates the flat CFG to its numbered explicit
graph, using the same three source instructions. -/
inductive Related (A B K D : τ) : Region Φ → Graph Φ A D → Type u where
  | generated (s : Loop Φ A B K D) : Related A B K D (region s) (graph s)

def lower (s : Loop Φ A B K D) : Σ g, Related A B K D (region s) g :=
  ⟨graph s, .generated s⟩

theorem Related.typing {r : Region Φ} {g : Graph Φ A D} (w : Related A B K D r g) :
    Region.HasType [A] r [D] :=
  match w with | .generated s => regionTyping s

def Related.checked {r : Region Φ} {g : Graph Φ A D} (w : Related A B K D r g) :
    NestedTheta.ExplicitRuntime.EntryChecked (a := carriedData (Carrier A D))
      (b := carriedData (Carrier A D)) g.toTerm :=
  match w with | .generated s => graphChecked s

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback
