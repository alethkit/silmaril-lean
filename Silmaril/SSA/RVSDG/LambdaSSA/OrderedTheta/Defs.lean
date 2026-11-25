module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms

/-! # One-block ΛSSA loops with an ordered RVSDG runtime -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta

open Silmaril.Isotope.LambdaSSA (Tm Region)
open OrderedRuntime.Structured

universe u

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

/-- The block instruction computes an exit payload or the next carried value. -/
structure Step (Φ : Type u) [HasTy Φ τ] (A : τ) where
  op : Φ
  input : instrSrc op = A
  output : instrTrg op = Silmaril.coprod A A

abbrev carried (A : τ) : Ports (OrderedRuntime.Structured.Ty τ) := [.value A]
abbrev results (A : τ) : Ports (OrderedRuntime.Structured.Ty τ) := .control 2 :: carried A

abbrev PureOp (τ : Type u) : Dialect.{u, u} τ PUnit := fun _ _ => PEmpty

inductive EffectOp (Φ : Type u) [HasTy Φ τ] : Dialect.{u, u} τ PUnit where
  | step {A : τ} : Step Φ A → EffectOp Φ (carried A) (results A)

abbrev Op (Φ : Type u) [HasTy Φ τ] := Opcode (PureOp τ) (EffectOp Φ)

variable {A : τ}

/-- Label zero is local. Label one is the unique external exit. -/
def block (op : Φ) : Region Φ :=
  .case (.op op (.var 0)) (.br 1 (.var 0)) (.br 0 (.var 0))

def region (op : Φ) : Region Φ := .cfg (.br 0 (.var 0)) 1 (fun _ => block op)

theorem Step.typing (step : Step Φ A) (Γ : List τ) :
    Tm.HasType (A :: Γ) (.op step.op (.var 0)) (Silmaril.coprod A A) := by
  have h : Tm.HasType (A :: Γ) (.var (Φ := Φ) 0) (instrSrc step.op) :=
    .var (congrArg some step.input.symm)
  exact step.output ▸ Tm.HasType.op h

theorem blockTyping (step : Step Φ A) :
    Region.HasType [A, A] (block step.op) [A, A] :=
  .case (step.typing [A]) (.br rfl (.var rfl)) (.br rfl (.var rfl))

theorem regionTyping (step : Step Φ A) : Region.HasType [A] (region step.op) [A] :=
  .cfg (fun _ => A) (.br rfl (.var rfl)) fun _ => blockTyping step

abbrev carriedData (A : τ) : Data (carried A) := .value .nil
abbrev resultData (A : τ) : Data (results A) := .control (carriedData A)

def inputWires (A : τ) : Wires (Threaded (carried A)) [] (carried A) :=
  .cons (.arg .head) .nil

def outputWires (A : τ) :
    Wires (Threaded (carried A)) [Threaded (results A)] (results A) :=
  .cons (.output 0 .head) (.cons (.output 0 (.tail .head)) .nil)

def body (s : Step Φ A) :
    Term (Op Φ) (Threaded (carried A)) [] [Threaded (results A)] (Threaded (results A)) :=
  .bind (primitiveNode (.arg (runtimePort (carried A))) (carriedData A) (resultData A)
    (.effect (EffectOp.step s)) (inputWires A)) (fun i => i.elim0)
    (.ret (withRuntime (nextRuntime [] (results A)) (outputWires A)))

def bodyChecked (s : Step Φ A) : EntryChecked (carriedData A) (resultData A) (body s) :=
  .bind (.arg (runtimePort (carried A))) (carriedData A) (resultData A)
    (.effect (EffectOp.step s)) (inputWires A) (.ret (nextRuntime [] (results A)) (outputWires A))

abbrev Loop (Φ : Type u) [HasTy Φ τ] (A : τ) :=
  OrderedRuntime.Structured.Theta.Loop (P := PureOp τ) (E := EffectOp Φ)
    (carried := carried A) (sigs := [Threaded (results A)])

def graph (s : Step Φ A) : Loop Φ A := ⟨(body s).toGraph⟩

def graphChecked (s : Step Φ A) :
    OrderedRuntime.Structured.Theta.BodyChecked (carriedData A) (graph s) :=
  (bodyChecked s).collect

inductive SSAForm (A : τ) : Region Φ → Type u where
  | loop (s : Step Φ A) : SSAForm A (region s.op)

inductive RVForm (A : τ) : Loop Φ A → Type u where
  | loop (s : Step Φ A) : RVForm A (graph s)

/-- The shared typed operation witnesses the relation between the fixed CFG
and graph wiring. No semantic equality occurs in the constructors. -/
inductive Related (A : τ) : Region Φ → Loop Φ A → Type u where
  | loop (s : Step Φ A) : Related A (region s.op) (graph s)

def lower {r : Region Φ} (h : SSAForm A r) : Σ g : Loop Φ A, Related A r g :=
  match h with
  | .loop s => ⟨graph s, .loop s⟩

def raise {g : Loop Φ A} (h : RVForm A g) : Σ r : Region Φ, Related A r g :=
  match h with
  | .loop s => ⟨region s.op, .loop s⟩

def Related.step {r : Region Φ} {g : Loop Φ A} (h : Related A r g) : Step Φ A :=
  match h with
  | .loop s => s

theorem Related.typing {r : Region Φ} {g : Loop Φ A} (h : Related A r g) :
    Region.HasType [A] r [A] := by
  cases h with
  | loop s => exact regionTyping s

def Related.checked {r : Region Φ} {g : Loop Φ A} (h : Related A r g) :
    OrderedRuntime.Structured.Theta.BodyChecked (carriedData A) g :=
  match h with
  | .loop s => graphChecked s

end Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta
