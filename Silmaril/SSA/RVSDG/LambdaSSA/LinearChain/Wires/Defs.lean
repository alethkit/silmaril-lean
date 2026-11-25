module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial.Defs

/-! # A numbered single-token elaboration of the typed body spine -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain

open Isotope.LambdaSSA (Region)
open TwoBlock.TwoExit (Carrier ExitCode Route headerPorts armPorts Pure)
open OrderedTheta (carried results carriedData resultData)
open OrderedRuntime.Structured (Data Threaded Opcode runtimePort nextRuntime newestIndex newestPort)
open NestedTheta.ExplicitRuntime (Checked EntryChecked)
open TwoBlock.ExplicitRuntime.Skeleton (Closed)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B C D : τ} {tail : List τ}

inductive Effect (Φ : Type u) [HasTy Φ τ] : Dialect.{u,u} τ PUnit where
  | header {A B C D : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod C B) →
      Effect Φ (carried (Carrier A C D)) (headerPorts B C D)
  | forward {B X C D : τ} : TwoBlock.Instruction Φ B X →
      Effect Φ (carried (Route B C D)) (carried (Route X C D))
  | last {A B C D : τ} : TwoBlock.Instruction Φ B (Silmaril.coprod D A) →
      Effect Φ (carried (Route B C D)) (results (Carrier A C D))

abbrev WireOp (Φ : Type u) [HasTy Φ τ] := Opcode (Pure τ) (Effect Φ)

namespace Wiring

open OrderedRuntime.Structured (Ty runtime)

abbrev carry (A C D : τ) := Threaded (carried (Carrier A C D))
abbrev result (A C D : τ) := Threaded (results (Carrier A C D))
abbrev intermediate (B C D : τ) := Threaded (carried (Route B C D))

/-- Each forward instruction reserves one numbered output signature. -/
def signatures (C : τ) : {B : τ} → {tail : List τ} → Body Φ A D B tail →
    List (Ports (OrderedRuntime.Structured.Ty τ))
  | _, _, .last _ => [result A C D]
  | _, _, .next (X := X) _ rest => intermediate X C D :: signatures C rest

/-- Select a typed port of the just-completed generator. -/
def newest {args out : Ports (OrderedRuntime.Structured.Ty τ)} {t : OrderedRuntime.Structured.Ty τ}
    (p : Port out t) (past : List (Ports (OrderedRuntime.Structured.Ty τ))) :
    Origin args (past ++ [out]) t :=
  .output (newestIndex out past) (newestPort p past)

/-- Compile a spine in any current scope. The next instruction can read
the value and token produced by its immediate predecessor. -/
def chain {args : Ports (OrderedRuntime.Structured.Ty τ)} (entryData : Data args) :
    {B : τ} → {tail : List τ} → (body : Body Φ A D B tail) →
    (past : List (Ports (OrderedRuntime.Structured.Ty τ))) →
    (live : Origin (Threaded args) past runtime) →
    (source : Origin (Threaded args) past (.value (Route B C D))) →
    Σ t : NestedTheta.Term (WireOp Φ) (Threaded args) past (signatures C body) (result A C D),
      Checked (Pure τ) (Effect Φ) entryData (resultData (Carrier A C D)) live t
  | _, _, .last op, past, live, source =>
    ⟨_, .primitive live (.value .nil) (resultData (Carrier A C D)) (.effect (Effect.last op)) (.cons source .nil)
      (.ret (nextRuntime past (results (Carrier A C D)))
        (.cons (newest .head past) (.cons (newest (.tail .head) past) .nil)))⟩
  | _, _, .next (X := X) op rest, past, live, source =>
    let child := chain entryData rest (past ++ [intermediate X C D])
      (nextRuntime past (carried (Route X C D))) (newest .head past)
    ⟨_, .primitive live (.value .nil) (.value .nil) (.effect (.forward op)) (.cons source .nil) child.2⟩

def bodyArm (body : Body Φ A D B tail) :
    Closed (Pure τ) (Effect Φ) (TwoBlock.ExplicitRuntime.Skeleton.armData (Carrier A C D) (Route B C D))
      (resultData (Carrier A C D)) (signatures C body) :=
  chain (.value (.value .nil)) body [] (.arg (runtimePort (armPorts A B C D))) (.arg (.tail .head))

def armSigs (body : Body Φ A D B tail) : Fin 2 → List (Ports (OrderedRuntime.Structured.Ty τ)) :=
  Fin.cases [result A C D] (fun _ => signatures C body)

def arms (body : Body Φ A D B tail) (i : Fin 2) :
    Closed (Pure τ) (Effect Φ) (TwoBlock.ExplicitRuntime.Skeleton.armData (Carrier A C D) (Route B C D))
      (resultData (Carrier A C D)) (armSigs (C := C) body i) :=
  Fin.cases (motive := fun j =>
    Closed (Pure τ) (Effect Φ) (TwoBlock.ExplicitRuntime.Skeleton.armData (Carrier A C D) (Route B C D))
      (resultData (Carrier A C D)) (armSigs (C := C) body j))
    (TwoBlock.ExplicitRuntime.Skeleton.arm (.pure Pure.exit)) (fun _ => bodyArm body) i

def thetaBody (s : Blocks Φ A B C D tail) :
    Closed (Pure τ) (Effect Φ) (carriedData (Carrier A C D)) (resultData (Carrier A C D))
      [Threaded (headerPorts B C D), result A C D] :=
  ⟨_, .primitive (.arg (runtimePort (carried (Carrier A C D)))) (carriedData (Carrier A C D))
    (.control (.value .nil)) (.effect (.header s.header)) (.cons (.arg .head) .nil)
    (.gamma (past := [Threaded (headerPorts B C D)]) 0 (.output (0 : Fin 1) .head)
      (nextRuntime [] (headerPorts B C D)) (.value (.value .nil)) (resultData (Carrier A C D))
      (.cons (.arg .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)) (armSigs s.body)
      (children := fun j => (arms s.body j).1) (fun j => (arms s.body j).2)
      (.ret (nextRuntime [Threaded (headerPorts B C D)] (results (Carrier A C D)))
        (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))⟩

def loop (s : Blocks Φ A B C D tail) :
    Closed (Pure τ) (Effect Φ) (carriedData (Carrier A C D)) (carriedData (Carrier A C D)) [carry A C D] :=
  ⟨_, .theta (.arg (runtimePort (carried (Carrier A C D)))) (carriedData (Carrier A C D)) (.cons (.arg .head) .nil)
    [Threaded (headerPorts B C D), result A C D] (children := fun _ => (thetaBody s).1)
    (fun _ => (thetaBody s).2)
    (.ret (nextRuntime [] (carried (Carrier A C D))) (.cons (.output (0 : Fin 1) .head) .nil))⟩

end Wiring

abbrev Loop (Φ : Type u) [HasTy Φ τ] (A C D : τ) :=
  TwoBlock.ExplicitRuntime.Skeleton.WireLoop (Pure τ) (Effect Φ) (Carrier A C D)

def graph (s : Blocks Φ A B C D tail) : Loop Φ A C D := (Wiring.loop s).1.toGraph

def graphChecked (s : Blocks Φ A B C D tail) :
    EntryChecked (a := carriedData (Carrier A C D)) (b := carriedData (Carrier A C D)) (graph s).toTerm :=
  (Wiring.loop s).2.collect

inductive SSAForm (A B C D : τ) (tail : List τ) : Region Φ → Type u where
  | loop (s : Blocks Φ A B C D tail) : SSAForm A B C D tail (region s)

inductive RVForm (A B C D : τ) (tail : List τ) : Loop Φ A C D → Type u where
  | loop (s : Blocks Φ A B C D tail) : RVForm A B C D tail (graph s)

inductive Related (A B C D : τ) (tail : List τ) : Region Φ → Loop Φ A C D → Type u where
  | loop (s : Blocks Φ A B C D tail) : Related A B C D tail (region s) (graph s)

def lower {r : Region Φ} (form : SSAForm A B C D tail r) : Σ g : Loop Φ A C D, Related A B C D tail r g :=
  match form with | .loop s => ⟨graph s, .loop s⟩

def raise {g : Loop Φ A C D} (form : RVForm A B C D tail g) : Σ r : Region Φ, Related A B C D tail r g :=
  match form with | .loop s => ⟨region s, .loop s⟩

def Related.instructions {r : Region Φ} {g : Loop Φ A C D} (rel : Related A B C D tail r g) : Blocks Φ A B C D tail :=
  match rel with | .loop s => s

theorem Related.typing {r : Region Φ} {g : Loop Φ A C D} (rel : Related A B C D tail r g) :
    Region.HasType [A] r [C,D] := by
  cases rel with
  | loop s => exact regionTyping s

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain
