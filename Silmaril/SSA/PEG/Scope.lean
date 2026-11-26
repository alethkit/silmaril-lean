module

public import Silmaril.SSA.PEG.Defs

/-! # Structural admission of cyclic PEGs

The edge roles make the three conditions of the paper's Definition 5.1
explicit. The stronger guard used by this library requires actual feedback
at a strictly enclosing loop on cycles through an eval or pass. The
well-foundedness of index-changing evaluation demands is a separate result.
-/

@[expose] public section

namespace Silmaril.SSA.PEG

universe u v w

/-- A finite dependency walk, recording each traversed edge's role in order. -/
inductive Walk {V : Type u} {K : Type v} (edge : V → K → V → Prop) :
    V → List K → V → Prop where
  | nil (a : V) : Walk edge a [] a
  | cons {a b c : V} {k : K} {ks : List K} :
      edge a k b → Walk edge b ks c → Walk edge a (k :: ks) c

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

def LoopForest.Up (f : LoopForest l) (inner : Fin l) (_ : Unit) (outer : Fin l) : Prop :=
  f.parent inner = some outer

/-- `Encloses outer inner` includes reflexivity. Traversal is from inner to outer. -/
def LoopForest.Encloses (f : LoopForest l) (outer inner : Fin l) : Prop :=
  ∃ ks, Walk f.Up inner ks outer

def LoopForest.StrictlyEncloses (f : LoopForest l) (outer inner : Fin l) : Prop :=
  ∃ ks, Walk f.Up inner ks outer ∧ ks ≠ []

/-- A finite parent table with no nonempty cycle is a rooted forest. -/
def LoopForest.WellFormed (f : LoopForest l) : Prop :=
  ∀ i, ¬f.StrictlyEncloses i i

def EdgeKind.IsFeedback {L : Type} : EdgeKind L → Prop
  | .feedback _ => True
  | _ => False

instance {L : Type} (k : EdgeKind L) : Decidable k.IsFeedback := by
  cases k <;> unfold EdgeKind.IsFeedback <;> infer_instance

/-- Traversing either arm of a θ witnesses the presence of its vertex. -/
def EdgeKind.IsThetaAt {L : Type} (l : L) (k : EdgeKind L) : Prop :=
  k = .initial l ∨ k = .feedback l

/-- A cycle can traverse eval's index argument or its sampled value. Pass only samples. -/
def EdgeKind.IsObserverAt {L : Type} (l : L) (k : EdgeKind L) : Prop :=
  k = .sample l ∨ k = .index l

/-- Definition 5.1(1). Removing θ's feedback edges leaves an acyclic graph. -/
def Graph.FeedbackCycles (g : Graph P params results n l) : Prop :=
  ∀ a ks, Walk g.Edge a ks a → ks ≠ [] → ∃ k ∈ ks, k.IsFeedback

/-- Definition 5.1(2). A path from a θ, eval or pass to a θ of a loop outside
the starting loop's ancestry must cross that target loop's sampling edge. -/
def Graph.Scoped (g : Graph P params results n l) : Prop :=
  ∀ a b ks start target, Walk g.Edge a ks b →
    (g.node a).label.loop = some start → (g.node b).label.thetaLoop = some target →
    g.forest.Encloses target start ∨ EdgeKind.sample target ∈ ks

/-- Definition 5.1(3) as printed. An outer θ vertex can be witnessed by its
initial edge. Kept as a separate predicate for comparison with the paper. -/
def Graph.OuterThetaCycles (g : Graph P params results n l) : Prop :=
  ∀ a ks, Walk g.Edge a ks a → ∀ k ∈ ks, ∀ inner, k.IsObserverAt inner →
    ∃ outer, g.forest.StrictlyEncloses outer inner ∧ ∃ e ∈ ks, e.IsThetaAt outer

/-- This strengthens Definition 5.1(3) to require outer iteration feedback
along the cycle, including at cycles entering eval through its index edge. -/
def Graph.OuterFeedbackCycles (g : Graph P params results n l) : Prop :=
  ∀ a ks, Walk g.Edge a ks a → ∀ k ∈ ks, ∀ inner, k.IsObserverAt inner →
    ∃ outer, g.forest.StrictlyEncloses outer inner ∧ EdgeKind.feedback outer ∈ ks

/-- The three printed graph clauses, interpreted in the ancestry order of
the chosen loop forest. The ordered-loop specialization requires the forest
itself to be valid. -/
structure Graph.PaperWellFormed (g : Graph P params results n l) : Prop where
  forest : g.forest.WellFormed
  feedback : g.FeedbackCycles
  loopScope : g.Scoped
  outerTheta : g.OuterThetaCycles

/-- Structural admission for the reusable core. -/
structure Graph.WellFormed (g : Graph P params results n l) : Prop where
  forest : g.forest.WellFormed
  feedback : g.FeedbackCycles
  loopScope : g.Scoped
  outerFeedback : g.OuterFeedbackCycles

end Silmaril.SSA.PEG
