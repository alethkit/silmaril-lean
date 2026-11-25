module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Lowering.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Defs

/-! # Constructor-wise numbering and runtime-token admission -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime

open Isotope.LambdaSSA (Region)
open OrderedTheta (carried results carriedData resultData)
open OrderedRuntime
open OrderedRuntime.Structured (Data Threaded runtime runtimePort nextRuntime)
open TwoBlock.TwoExit (Carrier ExitCode Route Pure headerPorts armPorts)
open TwoBlock.ExplicitRuntime.Skeleton (Closed WireLoop)
open NestedTheta.ExplicitRuntime (Checked EntryChecked)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K E D : τ}

inductive Effect (Φ : Type u) [HasTy Φ τ] : Dialect.{u,u} τ PUnit where
  | acyclic {ins outs : Ports (Structured.Ty τ)} : Acyclic.Opcode Φ ins outs → Effect Φ ins outs
  | header {A B E D : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod E B) →
      Effect Φ (carried (Carrier A E D)) (headerPorts B E D)
  | join {A K E D : τ} : TwoBlock.Instruction Φ K (Silmaril.coprod D A) →
      Effect Φ (carried K) (results (Carrier A E D))

abbrev Op (Φ : Type u) [HasTy Φ τ] := OrderedRuntime.Structured.Opcode (Pure τ) (Effect Φ)

namespace Wiring

open LinearChain.Wiring (newest)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

variable {args ins out outs : Ports (Structured.Ty τ)} {past : List (Ports (Structured.Ty τ))}
variable {a : Data args} {o : Data outs}

/-- An open region with numbered outputs and a checked current token. -/
abbrev Code (Φ : Type u) [HasTy Φ τ] (a : Data args) (o : Data outs)
    (live : Origin (Threaded args) past runtime) :=
  Σ sigs : List (Ports (Structured.Ty τ)), Σ t : NestedTheta.Term (Op Φ) (Threaded args) past sigs (Threaded outs),
    Checked (Pure τ) (Effect Φ) a o live t

abbrev Tail (Φ : Type u) [HasTy Φ τ] (a : Data args) (o : Data outs) (B : τ) :=
  (past : List (Ports (Structured.Ty τ))) → (live : Origin (Threaded args) past runtime) →
    Origin (Threaded args) past (.value B) → Code Φ a o live

def finish : Tail Φ a (carriedData B) B :=
  fun _ live source => ⟨[], _, .ret live (.cons source .nil)⟩

def primitive (i : Data ins) (d : Data out)
    (op : OrderedRuntime.Structured.Instruction (Pure τ) (Effect Φ) ins out)
    (live : Origin (Threaded args) past runtime) (inputs : Wires (Threaded args) past ins)
    (rest : Code Φ a o (nextRuntime past out)) : Code Φ a o live :=
  ⟨_, _, .primitive live i d op inputs rest.2.2⟩

def choice (i : Data ins) (d : Data out)
    (left right : Code (past := []) Φ i d (.arg (runtimePort ins)))
    (selector : Origin (Threaded args) past (.control 2))
    (live : Origin (Threaded args) past runtime) (inputs : Wires (Threaded args) past ins)
    (rest : Code Φ a o (nextRuntime past out)) : Code Φ a o live :=
  let arms : Fin 2 → Code (past := []) Φ i d (.arg (runtimePort ins)) :=
    Fin.cases left (fun _ => right)
  ⟨_, _, .gamma 0 selector live i d inputs (fun j => (arms j).1)
    (children := fun j => (arms j).2.1) (fun j => (arms j).2.2) rest.2.2⟩

/-- Recursion follows the acyclic grammar. The child boundary owns its own
token, and the continuation gets exactly the returned token of the selected
arm. Value origins and the token origin are tracked separately. -/
def emit : {A B : τ} → Body Φ A B → {args outs : Ports (Structured.Ty τ)} →
    {a : Data args} → {o : Data outs} → {past : List (Ports (Structured.Ty τ))} → {S : τ} →
    Input S A → (live : Origin (Threaded args) past runtime) →
    Origin (Threaded args) past (.value S) → Tail Φ a o B → Code Φ a o live
  | _, _, .instruction op, _, _, _, _, past, _, route, live, source, next =>
    primitive (carriedData _) (carriedData _) (.effect (.acyclic (.call route op))) live
      (.cons source .nil) (next _ (nextRuntime past _) (newest .head past))
  | _, _, .sequence first last, _, _, _, _, _, _, route, live, source, next =>
    emit first route live source (fun _ token value => emit last .direct token value next)
  | _, _, .choice (X := X) (Y := Y) op l r, _, _, _, _, past, _, route, live, source, next =>
    let inputs := carriedData (Silmaril.coprod X Y)
    let selected := results (Silmaril.coprod X Y)
    let left := emit l (past := []) .left (.arg (runtimePort _)) (.arg .head) finish
    let right := emit r (past := []) .right (.arg (runtimePort _)) (.arg .head) finish
    primitive (carriedData _) (resultData _) (.effect (.acyclic (.classify route op))) live
      (.cons source .nil)
      (choice inputs (carriedData _) left right (newest .head past)
        (nextRuntime past selected) (.cons (newest (.tail .head) past) .nil)
        (let before := past ++ [Threaded selected]
         next _ (nextRuntime before _) (newest .head before)))

def body (b : Body Φ A B) :
    Code (past := []) Φ (carriedData A) (carriedData B) (.arg (runtimePort (carried A))) :=
  emit b (past := []) .direct (.arg _) (.arg .head) finish

abbrev armData (A B E D : τ) : Data (armPorts A B E D) := .value (.value .nil)

def finishStep (past : List (Ports (Structured.Ty τ))) :
    Code Φ a (resultData (Carrier A E D)) (nextRuntime past (results (Carrier A E D))) :=
  ⟨[], _, .ret (nextRuntime past _) (.cons (newest .head past) (.cons (newest (.tail .head) past) .nil))⟩

def bodyArm (s : Loop Φ A B K E D) :
    Code (past := []) Φ (armData A B E D) (resultData (Carrier A E D)) (.arg (runtimePort (armPorts A B E D))) :=
  emit s.body (past := []) (.right (X := ExitCode E D)) (.arg _) (.arg (.tail .head)) fun past live value =>
    primitive (carriedData _) (resultData _) (.effect (.join s.join)) live (.cons value .nil) (finishStep past)

def exitArm :
    Code (past := []) Φ (armData A B E D) (resultData (Carrier A E D)) (.arg (runtimePort (armPorts A B E D))) :=
  primitive (past := []) (armData A B E D) (resultData _) (.pure .exit) (.arg _)
    (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) (finishStep [])

def thetaBody (s : Loop Φ A B K E D) :
    Code (past := []) Φ (carriedData (Carrier A E D)) (resultData (Carrier A E D))
      (.arg (runtimePort (carried (Carrier A E D)))) :=
  let header := headerPorts B E D
  primitive (past := []) (carriedData _) (resultData (Route B E D)) (.effect (.header s.header)) (.arg _)
    (.cons (.arg .head) .nil)
    (choice (armData A B E D) (resultData _) exitArm (bodyArm s)
      (newest .head []) (nextRuntime [] header)
      (.cons (.arg .head) (.cons (newest (.tail .head) []) .nil))
      (finishStep [Threaded header]))

def loop (s : Loop Φ A B K E D) :
    Closed (Pure τ) (Effect Φ) (carriedData (Carrier A E D)) (carriedData (Carrier A E D))
      [Threaded (carried (Carrier A E D))] :=
  ⟨_, .theta (.arg (runtimePort (carried (Carrier A E D)))) (carriedData _) (.cons (.arg .head) .nil)
    (thetaBody s).1 (children := fun _ => (thetaBody s).2.1) (fun _ => (thetaBody s).2.2)
    (.ret (nextRuntime [] (carried (Carrier A E D))) (.cons (newest .head []) .nil))⟩

end Wiring

/-- Numbered graphs at the loop boundary, with an independently indexed vertex table. -/
abbrev Numbered (Φ : Type u) [HasTy Φ τ] (A E D : τ)
    (sigs : List (Ports (Structured.Ty τ))) :=
  NestedTheta.Graph (Op Φ) (Threaded (carried (Carrier A E D))) [] sigs (Threaded (carried (Carrier A E D)))

abbrev Graph (Φ : Type u) [HasTy Φ τ] (A E D : τ) := WireLoop (Pure τ) (Effect Φ) (Carrier A E D)

def graph (s : Loop Φ A B K E D) : Graph Φ A E D := (Wiring.loop s).1.toGraph

def graphChecked (s : Loop Φ A B K E D) :
    EntryChecked (a := carriedData (Carrier A E D)) (b := carriedData (Carrier A E D)) (graph s).toTerm :=
  (Wiring.loop s).2.collect

/-- The actual typed source region and numbered graph are related by the
same header, recursive body and join instructions. -/
inductive Related (A B K E D : τ) : Region Φ → Graph Φ A E D → Type u where
  | loop (s : Loop Φ A B K E D) : Related A B K E D (region s) (graph s)

def elaborate (s : Loop Φ A B K E D) : Σ g, Related A B K E D (region s) g :=
  ⟨graph s, .loop s⟩

theorem Related.typing {r : Region Φ} {g : Graph Φ A E D}
    (w : Related A B K E D r g) : Region.HasType [A] r [E,D] := by
  cases w with | loop s => exact regionTyping s

def Related.checked {r : Region Φ} {g : Graph Φ A E D} (w : Related A B K E D r g) :
    EntryChecked (a := carriedData (Carrier A E D)) (b := carriedData (Carrier A E D)) g.toTerm :=
  match w with | .loop s => graphChecked s

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime
