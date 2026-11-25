module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial.Defs

/-! # A typed three-block loop and its numbered explicit runtime graph -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock

open Isotope.LambdaSSA (Region)
open TwoBlock.TwoExit (Carrier Route headerPorts armPorts Pure)
open OrderedTheta (carried results carriedData resultData)
open OrderedRuntime.Structured (Threaded Opcode Instruction runtimePort nextRuntime)
open TwoBlock.ExplicitRuntime.Skeleton (Closed)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B X C D : τ}

/-- The first body block has a separately typed outgoing parameter for the second block. -/
structure Blocks (Φ : Type u) [HasTy Φ τ] (A B X C D : τ) where
  header : TwoBlock.Instruction Φ A (Silmaril.coprod C B)
  first : TwoBlock.Instruction Φ B X
  last : TwoBlock.Instruction Φ X (Silmaril.coprod D A)

def header (op : Φ) : Region Φ := .case (.op op (.var 0)) (.br 3 (.var 0)) (.br 1 (.var 0))
def first (op : Φ) : Region Φ := .br 2 (.op op (.var 0))
def last (op : Φ) : Region Φ := .case (.op op (.var 0)) (.br 4 (.var 0)) (.br 0 (.var 0))

def localTypes (A B X : τ) : Fin 3 → τ := Fin.cases A (fun j => TwoBlock.localTypes B X j)

def blocks (h p q : Φ) : Fin 3 → Region Φ :=
  Fin.cases (header h) (Fin.cases (first p) (fun _ => last q))

def region (h p q : Φ) : Region Φ := .cfg (.br 0 (.var 0)) 3 (blocks h p q)

theorem headerTyping (s : Blocks Φ A B X C D) :
    Region.HasType [A, A] (header s.header.op) [A, B, X, C, D] :=
  .case (s.header.typing [A]) (.br rfl (.var rfl)) (.br rfl (.var rfl))

theorem firstTyping (s : Blocks Φ A B X C D) :
    Region.HasType [B, A] (first s.first.op) [A, B, X, C, D] :=
  .br rfl (s.first.typing [A])

theorem lastTyping (s : Blocks Φ A B X C D) :
    Region.HasType [X, A] (last s.last.op) [A, B, X, C, D] :=
  .case (s.last.typing [A]) (.br rfl (.var rfl)) (.br rfl (.var rfl))

theorem blockTyping (s : Blocks Φ A B X C D) (i : Fin 3) :
    Region.HasType (localTypes A B X i :: [A]) (blocks s.header.op s.first.op s.last.op i) [A, B, X, C, D] :=
  Fin.cases (motive := fun j => Region.HasType (localTypes A B X j :: [A])
    (blocks s.header.op s.first.op s.last.op j) [A, B, X, C, D])
    (headerTyping s) (Fin.cases (firstTyping s) (fun _ => lastTyping s)) i

theorem regionTyping (s : Blocks Φ A B X C D) :
    Region.HasType [A] (region s.header.op s.first.op s.last.op) [C, D] :=
  .cfg (localTypes A B X) (.br rfl (.var rfl)) (blockTyping s)

inductive Effect (Φ : Type u) [HasTy Φ τ] : Dialect.{u,u} τ PUnit where
  | header {A B C D : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod C B) →
      Effect Φ (carried (Carrier A C D)) (headerPorts B C D)
  | first {A B X C D : τ} : TwoBlock.Instruction Φ B X →
      Effect Φ (armPorts A B C D) (carried (Route X C D))
  | last {A X C D : τ} : TwoBlock.Instruction Φ X (Silmaril.coprod D A) →
      Effect Φ (carried (Route X C D)) (results (Carrier A C D))

abbrev WireOp (Φ : Type u) [HasTy Φ τ] := Opcode (Pure τ) (Effect Φ)

namespace Wiring

abbrev mid (X C D : τ) := Threaded (carried (Route X C D))
abbrev result (A C D : τ) := Threaded (results (Carrier A C D))
abbrev carry (A C D : τ) := Threaded (carried (Carrier A C D))

def armSigs (A X C D : τ) : Fin 2 → List (Ports (OrderedRuntime.Structured.Ty τ)) :=
  Fin.cases [result A C D] (fun _ => [mid X C D, result A C D])

/-- One typed producer and its token supply both inputs of the last block. -/
def bodyArm (s : Blocks Φ A B X C D) :
    Closed (Pure τ) (Effect Φ) (TwoBlock.ExplicitRuntime.Skeleton.armData (Carrier A C D) (Route B C D))
      (resultData (Carrier A C D)) [mid X C D, result A C D] :=
  ⟨_, .primitive (.arg (runtimePort (armPorts A B C D)))
    (.value (.value .nil)) (.value .nil) (.effect (.first s.first))
    (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.primitive (nextRuntime [] (carried (Route X C D))) (.value .nil) (resultData (Carrier A C D))
      (.effect (.last s.last)) (.cons (.output (0 : Fin 1) .head) .nil)
      (.ret (nextRuntime [mid X C D] (results (Carrier A C D)))
        (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))⟩

def arms (s : Blocks Φ A B X C D) (i : Fin 2) :
    Closed (Pure τ) (Effect Φ) (TwoBlock.ExplicitRuntime.Skeleton.armData (Carrier A C D) (Route B C D))
      (resultData (Carrier A C D)) (armSigs A X C D i) :=
  Fin.cases (motive := fun j =>
    Closed (Pure τ) (Effect Φ) (TwoBlock.ExplicitRuntime.Skeleton.armData (Carrier A C D) (Route B C D))
      (resultData (Carrier A C D)) (armSigs A X C D j))
    (TwoBlock.ExplicitRuntime.Skeleton.arm (.pure Pure.exit)) (fun _ => bodyArm s) i

def thetaBody (s : Blocks Φ A B X C D) :
    Closed (Pure τ) (Effect Φ) (carriedData (Carrier A C D)) (resultData (Carrier A C D))
      [Threaded (headerPorts B C D), result A C D] :=
  ⟨_, .primitive (.arg (runtimePort (carried (Carrier A C D)))) (carriedData (Carrier A C D))
    (.control (.value .nil)) (.effect (.header s.header)) (.cons (.arg .head) .nil)
    (.gamma (past := [Threaded (headerPorts B C D)]) 0 (.output (0 : Fin 1) .head)
      (nextRuntime [] (headerPorts B C D)) (.value (.value .nil)) (resultData (Carrier A C D))
      (.cons (.arg .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)) (armSigs A X C D)
      (children := fun j => (arms s j).1) (fun j => (arms s j).2)
      (.ret (nextRuntime [Threaded (headerPorts B C D)] (results (Carrier A C D)))
        (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))⟩

def loop (s : Blocks Φ A B X C D) :
    Closed (Pure τ) (Effect Φ) (carriedData (Carrier A C D)) (carriedData (Carrier A C D)) [carry A C D] :=
  ⟨_, .theta (.arg (runtimePort (carried (Carrier A C D)))) (carriedData (Carrier A C D)) (.cons (.arg .head) .nil)
    [Threaded (headerPorts B C D), result A C D] (children := fun _ => (thetaBody s).1)
    (fun _ => (thetaBody s).2)
    (.ret (nextRuntime [] (carried (Carrier A C D))) (.cons (.output (0 : Fin 1) .head) .nil))⟩

end Wiring

abbrev Loop (Φ : Type u) [HasTy Φ τ] (A C D : τ) :=
  TwoBlock.ExplicitRuntime.Skeleton.WireLoop (Pure τ) (Effect Φ) (Carrier A C D)

def graph (s : Blocks Φ A B X C D) : Loop Φ A C D := (Wiring.loop s).1.toGraph

def graphChecked (s : Blocks Φ A B X C D) :
    NestedTheta.ExplicitRuntime.EntryChecked (a := carriedData (Carrier A C D))
      (b := carriedData (Carrier A C D)) (graph s).toTerm :=
  (Wiring.loop s).2.collect

inductive SSAForm (A B X C D : τ) : Region Φ → Type u where
  | loop (s : Blocks Φ A B X C D) : SSAForm A B X C D (region s.header.op s.first.op s.last.op)

inductive RVForm (A B X C D : τ) : Loop Φ A C D → Type u where
  | loop (s : Blocks Φ A B X C D) : RVForm A B X C D (graph s)

/-- Syntax-directed correspondence between the real CFG and its checked numbered graph. -/
inductive Related (A B X C D : τ) : Region Φ → Loop Φ A C D → Type u where
  | loop (s : Blocks Φ A B X C D) : Related A B X C D (region s.header.op s.first.op s.last.op) (graph s)

def lower {r : Region Φ} (h : SSAForm A B X C D r) : Σ g : Loop Φ A C D, Related A B X C D r g :=
  match h with
  | .loop s => ⟨graph s, .loop s⟩

def raise {g : Loop Φ A C D} (h : RVForm A B X C D g) : Σ r : Region Φ, Related A B X C D r g :=
  match h with
  | .loop s => ⟨region s.header.op s.first.op s.last.op, .loop s⟩

def Related.instructions {r : Region Φ} {g : Loop Φ A C D} (h : Related A B X C D r g) :
    Blocks Φ A B X C D :=
  match h with
  | .loop s => s

theorem Related.typing {r : Region Φ} {g : Loop Φ A C D} (h : Related A B X C D r g) :
    Region.HasType [A] r [C, D] := by
  cases h with
  | loop s => exact regionTyping s

end Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock
