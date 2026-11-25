module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton.Defs

/-! # A numbered explicit-token elaboration of the typed two-block loop -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime

open OrderedTheta (carried results carriedData resultData)
open OrderedRuntime.Structured (Data Opcode Threaded)
open NestedTheta.ExplicitRuntime (EntryChecked)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B : τ}

abbrev WireOp (Φ : Type u) [HasTy Φ τ] := Opcode (Pure τ) (Effect Φ)

abbrev headerData (A B : τ) : Data (headerPorts A B) := .control (.value .nil)
abbrev armData (A B : τ) : Data (armPorts A B) := .value (.value .nil)

abbrev Closed (Φ : Type u) [HasTy Φ τ] {ins outs : Ports (OrderedRuntime.Structured.Ty τ)}
    (i : Data ins) (o : Data outs) (sigs : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  Skeleton.Closed (Pure τ) (Effect Φ) i o sigs

/-- Admit an arm with its own entry token and the primitive's returned token. -/
def arm (op : Op Φ (armPorts A B) (results A)) :
    Closed Φ (armData A B) (resultData A) [Threaded (results A)] :=
  Skeleton.arm (R := Silmaril.coprod A B) op

def arms (s : Blocks Φ A B) : Fin 2 → Closed Φ (armData A B) (resultData A) [Threaded (results A)] :=
  Fin.cases (arm (.pure Pure.exit)) (fun _ => arm (.effect (.body s.body)))

/-- Use the same numbered token wiring at all three nested boundaries. -/
def thetaBody (s : Blocks Φ A B) :
    Closed Φ (carriedData A) (resultData A) [Threaded (headerPorts A B), Threaded (results A)] :=
  Skeleton.thetaBody (.effect (.header s.header)) (arms s)

def loop (s : Blocks Φ A B) : Closed Φ (carriedData A) (carriedData A) [Threaded (carried A)] :=
  Skeleton.loop (.effect (.header s.header)) (arms s)

abbrev WireLoop (Φ : Type u) [HasTy Φ τ] (A : τ) :=
  Skeleton.WireLoop (Pure τ) (Effect Φ) A

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
