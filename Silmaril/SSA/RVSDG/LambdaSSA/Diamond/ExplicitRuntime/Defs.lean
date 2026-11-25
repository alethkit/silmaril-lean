module

public import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial.Defs

/-! # Numbered single-token lowering of the typed diamond CFG -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime

open Isotope.LambdaSSA (Region)
open OrderedTheta (carried results carriedData resultData)
open OrderedRuntime.Structured (Data Threaded Opcode runtimePort nextRuntime)
open TwoBlock.TwoExit (Carrier Pure headerPorts armPorts)
open TwoBlock.ExplicitRuntime.Skeleton (Closed headerData armData)
open NestedTheta.ExplicitRuntime (EntryChecked)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B X Y K E D : τ}

/-- Every effectful node carries exactly one source instruction. -/
inductive Effect (Φ : Type u) [HasTy Φ τ] : Dialect.{u,u} τ PUnit where
  | header {A B E D : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod E B) →
      Effect Φ (carried (Carrier A E D)) (headerPorts B E D)
  | classifier {A B X Y E D : τ} : TwoBlock.Instruction Φ B (Silmaril.coprod X Y) →
      Effect Φ (armPorts A B E D) (branchOut X Y)
  | left {X Y K : τ} : TwoBlock.Instruction Φ X K → Effect Φ (branchArgs X Y) (carried K)
  | right {X Y K : τ} : TwoBlock.Instruction Φ Y K → Effect Φ (branchArgs X Y) (carried K)
  | join {A K E D : τ} : TwoBlock.Instruction Φ K (Silmaril.coprod D A) →
      Effect Φ (carried K) (results (Carrier A E D))

namespace Wiring

abbrev carry (A E D : τ) := Threaded (carried (Carrier A E D))
abbrev result (A E D : τ) := Threaded (results (Carrier A E D))
abbrev select (X Y : τ) := Threaded (branchOut X Y)
abbrev joinValue (K : τ) := Threaded (carried K)

abbrev bodySigs (A X Y K E D : τ) := [select X Y, joinValue K, result A E D]

/-- An arm reads its selected payload and its boundary token. Its sole output
supplies both the join value and the next token. -/
def arm (op : Effect Φ (branchArgs X Y) (carried K)) :
    Closed (Pure τ) (Effect Φ) (carriedData (Silmaril.coprod X Y)) (carriedData K) [joinValue K] :=
  ⟨_, .primitive (.arg (runtimePort (branchArgs X Y))) (carriedData _) (carriedData K)
    (.effect op) (.cons (.arg .head) .nil)
    (.ret (nextRuntime [] (carried K)) (.cons (.output (0 : Fin 1) .head) .nil))⟩

def diamondArms (s : Branches Φ B X Y K) (i : Fin 2) :
    Closed (Pure τ) (Effect Φ) (carriedData (Silmaril.coprod X Y)) (carriedData K) [joinValue K] :=
  Fin.cases (arm (.left s.left)) (fun _ => arm (.right s.right)) i

/-- The inner γ passes only the selected arm the classifier's returned
token. Its output supplies the sole join node outside the two arms. -/
def bodyArm (s : Blocks Φ A B X Y K E D) :
    Closed (Pure τ) (Effect Φ) (TwoBlock.ExplicitRuntime.Skeleton.armData
      (Carrier A E D) (TwoBlock.TwoExit.Route B E D))
      (resultData (Carrier A E D)) (bodySigs A X Y K E D) :=
  ⟨_, .primitive (.arg (runtimePort (armPorts A B E D))) (.value (.value .nil)) (.control (.value .nil))
    (.effect (.classifier s.diamond.classifier)) (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.gamma (past := [select X Y]) 0 (.output (0 : Fin 1) .head) (nextRuntime [] (branchOut X Y))
      (carriedData (Silmaril.coprod X Y)) (carriedData K)
      (.cons (.output (0 : Fin 1) (.tail .head)) .nil) (fun _ => [joinValue K])
      (children := fun j => (diamondArms s.diamond j).1) (fun j => (diamondArms s.diamond j).2)
      (.primitive (nextRuntime [select X Y] (carried K)) (carriedData K) (resultData (Carrier A E D))
        (.effect (.join s.join)) (.cons (.output (1 : Fin 2) .head) .nil)
        (.ret (nextRuntime [select X Y, joinValue K] (results (Carrier A E D)))
          (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil)))))⟩

def outerSigs (A X Y K E D : τ) : Fin 2 → List (Ports (OrderedRuntime.Structured.Ty τ)) :=
  Fin.cases [result A E D] (fun _ => bodySigs A X Y K E D)

def outerArms (s : Blocks Φ A B X Y K E D) (i : Fin 2) :
    Closed (Pure τ) (Effect Φ) (armData (Carrier A E D) (TwoBlock.TwoExit.Route B E D))
      (resultData (Carrier A E D)) (outerSigs A X Y K E D i) :=
  Fin.cases (motive := fun j => Closed (Pure τ) (Effect Φ)
      (armData (Carrier A E D) (TwoBlock.TwoExit.Route B E D)) (resultData (Carrier A E D))
      (outerSigs A X Y K E D j))
    (TwoBlock.ExplicitRuntime.Skeleton.arm (.pure Pure.exit)) (fun _ => bodyArm s) i

def thetaBody (s : Blocks Φ A B X Y K E D) :
    Closed (Pure τ) (Effect Φ) (carriedData (Carrier A E D)) (resultData (Carrier A E D))
      [Threaded (headerPorts B E D), result A E D] :=
  ⟨_, .primitive (.arg (runtimePort (carried (Carrier A E D)))) (carriedData (Carrier A E D))
    (headerData _) (.effect (.header s.header)) (.cons (.arg .head) .nil)
    (.gamma (past := [Threaded (headerPorts B E D)]) 0 (.output (0 : Fin 1) .head)
      (nextRuntime [] (headerPorts B E D)) (armData (Carrier A E D) (TwoBlock.TwoExit.Route B E D))
      (resultData (Carrier A E D)) (.cons (.arg .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil))
      (outerSigs A X Y K E D) (children := fun j => (outerArms s j).1) (fun j => (outerArms s j).2)
      (.ret (nextRuntime [Threaded (headerPorts B E D)] (results (Carrier A E D)))
        (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))⟩

def loop (s : Blocks Φ A B X Y K E D) :
    Closed (Pure τ) (Effect Φ) (carriedData (Carrier A E D)) (carriedData (Carrier A E D)) [carry A E D] :=
  ⟨_, .theta (.arg (runtimePort (carried (Carrier A E D)))) (carriedData (Carrier A E D))
    (.cons (.arg .head) .nil) [Threaded (headerPorts B E D), result A E D]
    (children := fun _ => (thetaBody s).1) (fun _ => (thetaBody s).2)
    (.ret (nextRuntime [] (carried (Carrier A E D))) (.cons (.output (0 : Fin 1) .head) .nil))⟩

end Wiring

abbrev Loop (Φ : Type u) [HasTy Φ τ] (A E D : τ) :=
  TwoBlock.ExplicitRuntime.Skeleton.WireLoop (Pure τ) (Effect Φ) (Carrier A E D)

def graph (s : Blocks Φ A B X Y K E D) : Loop Φ A E D := (Wiring.loop s).1.toGraph

def graphChecked (s : Blocks Φ A B X Y K E D) :
    EntryChecked (a := carriedData (Carrier A E D)) (b := carriedData (Carrier A E D)) (graph s).toTerm :=
  (Wiring.loop s).2.collect

inductive SSAForm (A B X Y K E D : τ) : Region Φ → Type u where
  | loop (s : Blocks Φ A B X Y K E D) : SSAForm A B X Y K E D (region s)

inductive RVForm (A B X Y K E D : τ) : Loop Φ A E D → Type u where
  | loop (s : Blocks Φ A B X Y K E D) : RVForm A B X Y K E D (graph s)

inductive Related (A B X Y K E D : τ) : Region Φ → Loop Φ A E D → Type u where
  | loop (s : Blocks Φ A B X Y K E D) : Related A B X Y K E D (region s) (graph s)

def lower {r : Region Φ} (form : SSAForm A B X Y K E D r) :
    Σ g : Loop Φ A E D, Related A B X Y K E D r g :=
  match form with | .loop s => ⟨graph s, .loop s⟩

def raise {g : Loop Φ A E D} (form : RVForm A B X Y K E D g) :
    Σ r : Region Φ, Related A B X Y K E D r g :=
  match form with | .loop s => ⟨region s, .loop s⟩

def Related.instructions {r : Region Φ} {g : Loop Φ A E D}
    (h : Related A B X Y K E D r g) : Blocks Φ A B X Y K E D :=
  match h with | .loop s => s

theorem Related.typing {r : Region Φ} {g : Loop Φ A E D}
    (h : Related A B X Y K E D r g) : Region.HasType [A] r [E,D] := by
  cases h with | loop s => exact regionTyping s

def Related.checked {r : Region Φ} {g : Loop Φ A E D}
    (h : Related A B X Y K E D r g) :
    EntryChecked (a := carriedData (Carrier A E D)) (b := carriedData (Carrier A E D)) g.toTerm :=
  match h with | .loop s => graphChecked s

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime
