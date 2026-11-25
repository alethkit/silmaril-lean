module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Traces

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args args' outs outs' : Ports (PortType V S)} {sigs sigs' : List (Ports (PortType V S))}

theorem renumbering_nonempty {left : Graph Op args [] sigs outs} {right : Graph Op args' [] sigs' outs'}
    (iso : Graph.Isomorphic Op left right) : Nonempty (Renumbering Op left right) :=
  Isomorphism.Proofs.renumbering_nonempty iso

theorem Renumbering.isomorphic {left : Graph Op args [] sigs outs} {right : Graph Op args' [] sigs' outs'}
    (numbering : Renumbering Op left right) : Graph.Isomorphic Op left right :=
  Isomorphism.Proofs.numbering_isomorphic numbering

theorem Renumbering.initial_matches {left : Graph Op args [] sigs outs} {right : Graph Op args' [] sigs' outs'}
    (numbering : Renumbering Op left right) (m : Model.{u, v, w} Op) :
    numbering.Matches m (initial m left) (initial m right) :=
  (Isomorphism.Proofs.laws m numbering).pending

/-- Every typed marking has exactly one image under the fixed maps,
including all data in its live child regions. -/
theorem Renumbering.marking_forth {left : Graph Op args [] sigs outs} {right : Graph Op args' [] sigs' outs'}
    (numbering : Renumbering Op left right) (m : Model.{u, v, w} Op) (a : GraphMarking m left) :
    ∃! b : GraphMarking m right, numbering.Matches m a b :=
  (Isomorphism.Proofs.laws m numbering).unique_right a

/-- Every typed marking has exactly one preimage under the fixed maps. -/
theorem Renumbering.marking_back {left : Graph Op args [] sigs outs} {right : Graph Op args' [] sigs' outs'}
    (numbering : Renumbering Op left right) (m : Model.{u, v, w} Op) (b : GraphMarking m right) :
    ∃! a : GraphMarking m left, numbering.Matches m a b :=
  (Isomorphism.Proofs.laws m numbering).unique_left b

theorem Steps.of_reaches {L : Type w} {step : L → L → Prop} {a b : L}
    (trace : Relation.ReflTransGen step a b) : ∃ n, Steps step n a b :=
  Isomorphism.Proofs.count_trace trace

variable {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}

/-- The result read from two matching markings agrees, including when both
markings still have uncompleted vertices. -/
theorem Renumbering.result_eq (numbering : Renumbering Op left right) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) {a : GraphMarking m left} {b : GraphMarking m right}
    (matched : numbering.Matches m a b) : result m left input a = result m right input b :=
  Isomorphism.Proofs.option_colours_injective ((Isomorphism.Proofs.laws m numbering).finished (inputL := input) rfl matched)

/-- Match one firing on the left by exactly one firing on the right. The
relation compares live children and needs no separate reachability premise. -/
theorem Renumbering.step_forth (numbering : Renumbering Op left right) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) {a a' : GraphMarking m left} {b : GraphMarking m right}
    (matched : numbering.Matches m a b) (step : Step m left input a a') :
    ∃ b', Step m right input b b' ∧ numbering.Matches m a' b' :=
  (Isomorphism.Proofs.laws m numbering).forth (inputL := input) rfl matched step

theorem Renumbering.step_back (numbering : Renumbering Op left right) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) {a : GraphMarking m left} {b b' : GraphMarking m right}
    (matched : numbering.Matches m a b) (step : Step m right input b b') :
    ∃ a', Step m left input a a' ∧ numbering.Matches m a' b' :=
  (Isomorphism.Proofs.laws m numbering).back (inputL := input) rfl matched step

/-- The unique marking correspondence preserves and reflects one-step firing. -/
theorem Renumbering.step_iff (numbering : Renumbering Op left right) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) {a a' : GraphMarking m left} {b b' : GraphMarking m right}
    (before : numbering.Matches m a b) (after : numbering.Matches m a' b') :
    Step m left input a a' ↔ Step m right input b b' :=
  (Isomorphism.Proofs.laws m numbering).step_iff m (inputL := input) rfl before after

/-- Match a finite trace of the same length, with related markings at every step. -/
theorem Renumbering.trace_forth (numbering : Renumbering Op left right) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) {n : Nat} {a a' : GraphMarking m left} {b : GraphMarking m right}
    (matched : numbering.Matches m a b) (trace : Steps (Step m left input) n a a') :
    ∃ b', PairedSteps (Step m left input) (Step m right input) (numbering.Matches m) n a b a' b' :=
  Isomorphism.Proofs.pair_left (fun h step => numbering.step_forth m input h step) matched trace

theorem Renumbering.trace_back (numbering : Renumbering Op left right) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) {n : Nat} {a : GraphMarking m left} {b b' : GraphMarking m right}
    (matched : numbering.Matches m a b) (trace : Steps (Step m right input) n b b') :
    ∃ a', PairedSteps (Step m left input) (Step m right input) (numbering.Matches m) n a b a' b' :=
  Isomorphism.Proofs.pair_right (fun h step => numbering.step_back m input h step) matched trace

end Silmaril.SSA.RVSDG.NestedTheta.Petri
