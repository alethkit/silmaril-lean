module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Defs

/-! # A flat diamond with a loop in each arm and a shared continuation -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond

open Isotope.LambdaSSA (Region)
open Sequential
open OrderedTheta (carried carriedData results resultData)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open TwoBlock.TwoExit (Carrier Pure)
open NestedTheta.ExplicitRuntime (EntryChecked)
open NestedTheta.ExplicitRuntime.Splice (Code append)
open LinearChain.Wiring (newest)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A M Y E D : τ}

/-- The arms may have different entry and body types. Both of their exits
supply the same join type; the shared continuation has two typed exits. -/
structure Diamond (Φ : Type u) [HasTy Φ τ] (A M Y E D : τ) where
  gate : TwoBlock.Instruction Φ A (Carrier Y M M)
  leftBody : τ
  leftJoin : τ
  rightBody : τ
  rightJoin : τ
  nextBody : τ
  nextJoin : τ
  left : Loop Φ M leftBody leftJoin M M
  right : Loop Φ Y rightBody rightJoin M M
  next : Loop Φ M nextBody nextJoin E D

def source (s : Diamond Φ A M Y E D) : Flat.Fragment Φ A E D :=
  Flat.link (Flat.fork (.loop s.left) (.loop s.right) s.gate) (.loop s.next)

abbrev Branch (M Y : τ) := Carrier Y M M
abbrev Result (M E D : τ) := Carrier M E D
abbrev Signatures (M Y E D : τ) :=
  [Threaded (results (Branch M Y)), Threaded (carried (Result M E D)), Threaded (carried (Result M E D))]

abbrev Graph (Φ : Type u) [HasTy Φ τ] (A M Y E D : τ) :=
  NestedTheta.Graph (Wires.Op Φ) (Threaded (carried A)) [] (Signatures M Y E D)
    (Threaded (carried (Result M E D)))

namespace Wiring

def left (s : Diamond Φ A M Y E D) :
    Code (past := []) (Pure τ) (Wires.Effect Φ) (carriedData (Branch M Y)) (carriedData (Result M E D))
      (.arg (runtimePort _))
      [Threaded (carried (Branch M M)), Threaded (carried (Branch M M)), Threaded (carried (Result M E D))] :=
  let intoLoop := Flat.Numbered.connector (Φ := Φ) (I := Y) (M := M) (E := M) (D := M)
  let loop := Wires.liftChecked (ExplicitRuntime.Wiring.loop s.left).2
  let intoJoin := Flat.Numbered.connector (Φ := Φ) (I := M) (M := M) (E := E) (D := D)
  append intoJoin.2 (append loop.2 intoLoop.2).2

def right (s : Diamond Φ A M Y E D) :
    Code (past := []) (Pure τ) (Wires.Effect Φ) (carriedData (Branch M Y)) (carriedData (Result M E D))
      (.arg (runtimePort _))
      [Threaded (carried (Branch M Y)), Threaded (carried (Result M E D))] :=
  append (Flat.Numbered.connector (Φ := Φ) (I := Y) (M := M) (E := E) (D := D)).2
    (Wires.liftChecked (ExplicitRuntime.Wiring.loop s.right).2).2

def select (s : Diamond Φ A M Y E D) :
    Code (past := []) (Pure τ) (Wires.Effect Φ) (carriedData A) (carriedData (Result M E D))
      (.arg (runtimePort _))
      [Threaded (results (Branch M Y)), Threaded (carried (Result M E D))] :=
  let classified := results (Branch M Y)
  let joined := carried (Result M E D)
  let before := [Threaded classified]
  let arms j := Fin.cases (motive := fun (_ : Fin 2) =>
    Σ sigs, Code (past := []) (Pure τ) (Wires.Effect Φ) (carriedData (Branch M Y))
      (carriedData (Result M E D)) (.arg (runtimePort _)) sigs)
    ⟨_, left s⟩ (fun _ => ⟨_, right s⟩) j
  ⟨_, .primitive (.arg (runtimePort (carried A))) (carriedData A) (resultData (Branch M Y))
    (.effect (.loop (.acyclic (.classify .direct s.gate)))) (.cons (.arg .head) .nil) <|
      .gamma 0 (newest .head []) (nextRuntime [] classified) (carriedData (Branch M Y))
        (carriedData (Result M E D)) (.cons (newest (.tail .head) []) .nil) (fun j => (arms j).1)
        (children := fun j => (arms j).2.1) (fun j => (arms j).2.2)
        (.ret (nextRuntime before joined) (.cons (newest .head before) .nil))⟩

def code (s : Diamond Φ A M Y E D) :
    Code (past := []) (Pure τ) (Wires.Effect Φ) (carriedData A) (carriedData (Result M E D))
      (.arg (runtimePort _)) (Signatures M Y E D) :=
  append (Wires.liftChecked (ExplicitRuntime.Wiring.loop s.next).2).2 (select s).2

end Wiring

def graph (s : Diamond Φ A M Y E D) : Graph Φ A M Y E D := (Wiring.code s).1.toGraph

def graphChecked (s : Diamond Φ A M Y E D) :
    EntryChecked (a := carriedData A) (b := carriedData (Result M E D)) (graph s).toTerm :=
  (Wiring.code s).2.collect

inductive Source (A M Y E D : τ) : Region Φ → Type u where
  | diamond (s : Diamond Φ A M Y E D) : Source A M Y E D (source s).region

inductive Related (A M Y E D : τ) : Region Φ → Graph Φ A M Y E D → Type u where
  | diamond (s : Diamond Φ A M Y E D) : Related A M Y E D (source s).region (graph s)

def lower {r : Region Φ} (w : Source A M Y E D r) :
    Σ g : Graph Φ A M Y E D, Related A M Y E D r g :=
  match w with | .diamond s => ⟨graph s, .diamond s⟩

theorem Related.typing {r : Region Φ} {g : Graph Φ A M Y E D} (w : Related A M Y E D r g) :
    Region.HasType [A] r [E,D] :=
  match w with | .diamond s => (source s).typing

def Related.checked {r : Region Φ} {g : Graph Φ A M Y E D} (w : Related A M Y E D r g) :
    EntryChecked (a := carriedData A) (b := carriedData (Result M E D)) g.toTerm :=
  match w with | .diamond s => graphChecked s

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond
