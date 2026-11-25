module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs
public import Silmaril.SSA.RVSDG.Theta.Defs

/-! # One-block tail-controlled λSSA and whole-region RVSDG θ -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta

open Silmaril.Isotope.LambdaSSA (Tm Region)

universe u v
variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- A dialect instruction consumes the carried value and returns either a
finished value (left) or an updated value for the back edge (right). -/
structure Step (Φ : Type v) [HasTy Φ τ] (A : τ) where
  op : Φ
  input : instrSrc (τ := τ) op = A
  output : instrTrg (τ := τ) op = Silmaril.coprod A A

abbrev Ty (τ : Type u) := PortType τ PEmpty

abbrev carried (A : τ) : Ports (Ty τ) := [.value A]
abbrev results (A : τ) : Ports (Ty τ) := RVSDG.Theta.BodyResults (carried A)

/-- The same typed step returns the selector and payload on separate ports. -/
inductive Opcode (Φ : Type v) [HasTy Φ τ] : Dialect.{u, max u v} τ PEmpty where
  | step {A : τ} : Step Φ A → Opcode Φ (carried A) (results A)

variable {A : τ}

/-- The entry jumps to the unique local label. The block parameter is
variable zero, and the case payload is variable zero in each arm. -/
def block (op : Φ) : Region Φ :=
  .case (.op op (.var 0)) (.br 1 (.var 0)) (.br 0 (.var 0))

def region (op : Φ) : Region Φ :=
  .cfg (.br 0 (.var 0)) 1 (fun _ => block op)

def body (step : Step Φ A) : Term (Opcode Φ) (carried A) [] [results A] (results A) :=
  let node : Node (Opcode Φ) (carried A) [] (results A) :=
    ⟨carried A, .simple (.step step), .cons (.arg .head) .nil, fun i => i.elim0⟩
  .bind node (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

abbrev LoopGraph (Φ : Type v) [HasTy Φ τ] (A : τ) :=
  RVSDG.Theta.Graph (Opcode Φ) (carried A) [results A]

def graph (step : Step Φ A) : LoopGraph Φ A := ⟨(body step).toGraph⟩

/-- Syntactic admission of a real one-block λSSA CFG with one external exit. -/
inductive SSAForm (A : τ) : Region Φ → Type v where
  | loop (step : Step Φ A) : SSAForm A (region step.op)

/-- Syntactic admission of a graph with a single correctly wired step vertex. -/
inductive RVForm (A : τ) : LoopGraph Φ A → Type v where
  | loop (step : Step Φ A) : RVForm A (graph step)

/-- The witness identifies the typed dialect step shared by both syntaxes. -/
inductive Related (A : τ) : Region Φ → LoopGraph Φ A → Type v where
  | loop (step : Step Φ A) : Related A (region step.op) (graph step)

def lower {r : Region Φ} (h : SSAForm A r) : Σ g : LoopGraph Φ A, Related A r g :=
  match h with
  | .loop step => ⟨graph step, .loop step⟩

def raise {g : LoopGraph Φ A} (h : RVForm A g) : Σ r : Region Φ, Related A r g :=
  match h with
  | .loop step => ⟨region step.op, .loop step⟩

/-- The actual typing of a step expression in a block that can read a
surrounding context. Its only operand is the local block parameter. -/
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

theorem Related.typing {r : Region Φ} {g : LoopGraph Φ A} (h : Related A r g) :
    Region.HasType [A] r [A] := by
  cases h with
  | loop step => exact regionTyping step

end Silmaril.SSA.RVSDG.LambdaSSA.Theta
