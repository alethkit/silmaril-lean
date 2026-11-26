module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Thms
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Maps of feedback graphs with a fixed external interface -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

universe v w x

variable {τ : Type v} {R S L : List τ} {α : Type w} {σ : Type x}

/-- A deterministic map that preserves the payload type of each block label. -/
structure LabelMap (R S : List τ) where
  label : Fin R.length → Fin S.length
  type_eq : ∀ i, S.get (label i) = R.get i

/-- Keep entry states, payloads, and machine states when changing block labels. -/
def Point.map {n m : Nat} (label : Fin n → Fin m) : Point n α σ → Point m α σ
  | .entry s => .entry s
  | .block i a s => .block (label i) a s

/-- Forward transfer and backward lifting are required only at source points
reachable from the chosen start. Backward lifting must match the selected
target successor, including its payload and state. -/
structure Bisimulation (f : Run R L α σ) (g : Run S L α σ)
    (map : Point R.length α σ → Point S.length α σ) (start : Point R.length α σ) : Prop where
  forward : ∀ {p q}, Reaches f start p → Step f p q → Step g (map p) (map q)
  backward : ∀ {p q}, Reaches f start p → Step g (map p) q →
    ∃ next, Step f p next ∧ map next = q
  top : ∀ {p}, Reaches f start p → (f p = ⊤ ↔ g (map p) = ⊤)
  outcome : ∀ {p}, Reaches f start p → ∀ o : Outcome L.length α σ,
    (f p).Ordinary (external R L o) ↔ (g (map p)).Ordinary (external S L o)

/-- The native order of the internal prefix and external suffix. -/
def labelEquiv (R L : List τ) : Fin R.length ⊕ Fin L.length ≃ Fin (R ++ L).length :=
  finSumFinEquiv.trans (finCongr (@List.length_append _ R L).symm)

/-- Route internal labels through a deterministic map and keep external labels. -/
def mapLabel (label : Fin R.length → Fin S.length) (L : List τ)
    (i : Fin (R ++ L).length) : Fin (S ++ L).length :=
  labelEquiv S L (Sum.map label id ((labelEquiv R L).symm i))

def mapOutcome (label : Fin R.length → Fin S.length) :
    Outcome (R ++ L).length α σ → Outcome (S ++ L).length α σ
  | .ret i a s => .ret (mapLabel label L i) a s
  | .fault s => .fault s
  | .diverge => .diverge

/-- Map ordinary returns, preserving faults, divergence, and fresh top. -/
def mapReturns (label : Fin R.length → Fin S.length)
    (b : Behaviour (R ++ L).length α σ) : Behaviour (S ++ L).length α σ :=
  b.map (Set.image (mapOutcome label))

/-- Move the block invocations and ordinary internal returns together. -/
def relabel (e : Fin R.length ≃ Fin S.length) (f : Run R L α σ) : Run S L α σ :=
  fun q => mapReturns e (f (q.map e.symm))

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback
