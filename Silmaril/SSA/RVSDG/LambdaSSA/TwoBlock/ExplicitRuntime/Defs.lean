module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms

/-! # A numbered explicit-token elaboration of the typed two-block loop -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime

open OrderedTheta (carried results carriedData resultData)
open OrderedRuntime.Structured (Ty Data Opcode Threaded runtimePort nextRuntime)
open NestedTheta.ExplicitRuntime (EntryChecked Checked)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B : τ}

abbrev WireOp (Φ : Type u) [HasTy Φ τ] := Opcode (Pure τ) (Effect Φ)

abbrev headerData (A B : τ) : Data (headerPorts A B) := .control (.value .nil)
abbrev armData (A B : τ) : Data (armPorts A B) := .value (.value .nil)

abbrev Closed (Φ : Type u) [HasTy Φ τ] {ins outs : Ports (OrderedRuntime.Structured.Ty τ)}
    (i : Data ins) (o : Data outs) (sigs : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  Σ t : NestedTheta.Term (WireOp Φ) (Threaded ins) [] sigs (Threaded outs),
    EntryChecked (a := i) (b := o) t

/-- Admit an arm with its own entry token and the primitive's returned token. -/
def arm (op : Op Φ (armPorts A B) (results A)) :
    Closed Φ (armData A B) (resultData A) [Threaded (results A)] :=
  ⟨_, .primitive (.arg (runtimePort (armPorts A B))) (armData A B) (resultData A) op
    (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.ret (nextRuntime [] (results A))
      (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))⟩

def arms (s : Blocks Φ A B) : Fin 2 → Closed Φ (armData A B) (resultData A) [Threaded (results A)] :=
  Fin.cases (arm (.pure Pure.exit)) (fun _ => arm (.effect (.body s.body)))

/-- The γ receives the header's returned token. Both arms return into the
same typed γ result, whose token is sent to the θ decision. -/
def thetaBody (s : Blocks Φ A B) :
    Closed Φ (carriedData A) (resultData A) [Threaded (headerPorts A B), Threaded (results A)] :=
  ⟨_, .primitive (.arg (runtimePort (carried A))) (carriedData A) (headerData A B)
    (.effect (.header s.header)) (.cons (.arg .head) .nil)
    (.gamma (past := [Threaded (headerPorts A B)]) 0 (.output (0 : Fin 1) .head)
      (nextRuntime [] (headerPorts A B)) (armData A B) (resultData A)
      (.cons (.arg .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)) (fun _ => [Threaded (results A)])
      (children := fun j => (arms s j).1) (fun j => (arms s j).2)
      (.ret (nextRuntime [Threaded (headerPorts A B)] (results A))
        (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))⟩

def loop (s : Blocks Φ A B) : Closed Φ (carriedData A) (carriedData A) [Threaded (carried A)] :=
  ⟨_, .theta (.arg (runtimePort (carried A))) (carriedData A) (.cons (.arg .head) .nil)
    [Threaded (headerPorts A B), Threaded (results A)] (children := fun _ => (thetaBody s).1)
    (fun _ => (thetaBody s).2) (.ret (nextRuntime [] (carried A)) (.cons (.output (0 : Fin 1) .head) .nil))⟩

abbrev WireLoop (Φ : Type u) [HasTy Φ τ] (A : τ) :=
  NestedTheta.Graph (WireOp Φ) (Threaded (carried A)) [] [Threaded (carried A)] (Threaded (carried A))

def graph (s : Blocks Φ A B) : WireLoop Φ A := (loop s).1.toGraph

def graphChecked (s : Blocks Φ A B) : EntryChecked (a := carriedData A) (b := carriedData A) (graph s).toTerm :=
  (loop s).2.collect

open Isotope.LetIter.ProofRelevant.Semantics

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable [InstructionModel Φ τ ε (StateM σ)] [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- The partial model lifts each total instruction with its final state intact. -/
def PrimitiveAgreement (Φ : Type u) [HasTy Φ τ] [HasEff Φ ε]
    [InstructionModel Φ τ ε (StateM σ)] [InstructionModel Φ τ ε (StateT σ Part.{u})] : Prop :=
  ∀ (op : Φ) (x : TyDen (τ := τ) (instrSrc op)) (state : σ),
    (InstructionModel.denote (ε := ε) (m := StateT σ Part.{u}) op x).run state =
      Part.some ((InstructionModel.denote (ε := ε) (m := StateM σ) op x).run state)

abbrev wireModel := orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateM σ)

/-- Read the erased numbered graph at the LambdaSSA exit, retaining its state. -/
noncomputable def erasedObservation (s : Blocks Φ A B) (a : TyDen A) (state : σ) :
    Part (Isotope.LambdaSSA.Semantics.Monadic.LabelDen [A] × σ) :=
  (fun output => (OrderedTheta.exit (output.1.get .head), output.2)) <$>
    NestedTheta.ExplicitRuntime.observe (wireModel (ε := ε) (σ := σ)) (graph s) (graphChecked s)
      (OrderedTheta.point a state)

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime
