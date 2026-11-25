module

public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms

/-! # Token wiring for a header followed by one of two arms -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton

open OrderedTheta (carried results carriedData resultData)
open OrderedRuntime.Structured (Data Opcode Threaded runtimePort nextRuntime)
open NestedTheta.ExplicitRuntime (EntryChecked)

universe u
variable {τ : Type u} {P E : Dialect.{u,u} τ PUnit}
variable {K R : τ}

abbrev headerPorts (R : τ) : Ports (OrderedRuntime.Structured.Ty τ) := [.control 2, .value R]
abbrev armPorts (K R : τ) : Ports (OrderedRuntime.Structured.Ty τ) := [.value K, .value R]
abbrev headerData (R : τ) : Data (headerPorts R) := .control (.value .nil)
abbrev armData (K R : τ) : Data (armPorts K R) := .value (.value .nil)

abbrev Closed (P E : Dialect.{u,u} τ PUnit) {ins outs : Ports (OrderedRuntime.Structured.Ty τ)}
    (i : Data ins) (o : Data outs) (sigs : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  Σ t : NestedTheta.Term (Opcode P E) (Threaded ins) [] sigs (Threaded outs),
    EntryChecked (a := i) (b := o) t

abbrev Arm (P E : Dialect.{u,u} τ PUnit) (K R : τ) :=
  OrderedRuntime.Structured.Instruction P E (armPorts K R) (results K)

def arm (op : Arm P E K R) :
    Closed P E (armData K R) (resultData K) [Threaded (results K)] :=
  ⟨_, .primitive (.arg (runtimePort (armPorts K R))) (armData K R) (resultData K) op
    (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.ret (nextRuntime [] (results K))
      (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))⟩

variable (header : OrderedRuntime.Structured.Instruction P E (carried K) (headerPorts R))
variable (arms : Fin 2 → Closed P E (armData K R) (resultData K) [Threaded (results K)])

/-- γ receives the header's returned token. Each arm has its own entry
token and returns the single token that θ uses for feedback or exit. -/
def thetaBody :
    Closed P E (carriedData K) (resultData K) [Threaded (headerPorts R), Threaded (results K)] :=
  ⟨_, .primitive (.arg (runtimePort (carried K))) (carriedData K) (headerData R)
    header (.cons (.arg .head) .nil)
    (.gamma (past := [Threaded (headerPorts R)]) 0 (.output (0 : Fin 1) .head)
      (nextRuntime [] (headerPorts R)) (armData K R) (resultData K)
      (.cons (.arg .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)) (fun _ => [Threaded (results K)])
      (children := fun j => (arms j).1) (fun j => (arms j).2)
      (.ret (nextRuntime [Threaded (headerPorts R)] (results K))
        (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))⟩

def loop : Closed P E (carriedData K) (carriedData K) [Threaded (carried K)] :=
  ⟨_, .theta (.arg (runtimePort (carried K))) (carriedData K) (.cons (.arg .head) .nil)
    [Threaded (headerPorts R), Threaded (results K)] (children := fun _ => (thetaBody header arms).1)
    (fun _ => (thetaBody header arms).2)
    (.ret (nextRuntime [] (carried K)) (.cons (.output (0 : Fin 1) .head) .nil))⟩

abbrev WireLoop (P E : Dialect.{u,u} τ PUnit) (K : τ) :=
  NestedTheta.Graph (Opcode P E) (Threaded (carried K)) [] [Threaded (carried K)] (Threaded (carried K))

def graph : WireLoop P E K := (loop header arms).1.toGraph

def graphChecked : EntryChecked (a := carriedData K) (b := carriedData K) (graph header arms).toTerm :=
  (loop header arms).2.collect

variable {F : τ → Type u} {σ : Type u}

/-- Add the live state to a single carried value. -/
def point (a : F K) (state : σ) : Tuple (OrderedRuntime.Structured.RuntimeValues F σ) (Threaded (carried K)) :=
  .cons a (.cons state .nil)

/-- Encode the outcome of one activation at the explicit θ boundary. -/
def tagged {X Y : Type u} (enter : X → F K) (finish : Y → F K) (result : (Y ⊕ X) × σ) :
    Tuple (OrderedRuntime.Structured.RuntimeValues F σ) (Threaded (results K)) :=
  match result.1 with
  | .inl out => .cons ⟨0⟩ (point (finish out) result.2)
  | .inr next => .cons ⟨1⟩ (point (enter next) result.2)

/-- Read the payload after erasure and observe the single live token separately. -/
noncomputable def observeCarrier (m : OrderedRuntime.Structured.Model P E (StateM σ))
    (input : m.value K) (state : σ) : Part (m.value K × σ) :=
  (fun output => (output.1.get .head, output.2)) <$>
    NestedTheta.ExplicitRuntime.observe m (graph header arms) (graphChecked header arms) (point input state)

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton
