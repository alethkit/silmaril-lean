module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution.Adequacy

/-! Adequacy of the compiled equations in the existing λSSA observational room. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution

open CategoryTheory
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → NativeSignature, Model → NativeModel, Equation → NativeEquation
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution (mapGraph reduct)
open Isotope (Value)
open Isotope.Institution.Observational (Observation ssaBeh)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open Isotope.Morphism.SSAIter (ScopedRegion)

variable {P Q : NativeSignature}

/-- The model's bound values give exactly the lowering's entry environment
on the scope of any region with this boundary. -/
theorem ret_mem_eval (m : NativeModel P) (guard : Bool)
    (region : ScopedRegion Opcode 1 (entryContext P.args).length)
    (initial final : Heap m.cells) (label : Nat) (payload : Value (Atom m.cells)) :
    Observation.ret initial (label, payload) final ∈ ssaBeh 1 (entryModel m guard) region ↔
      Eval (Instruction m.cells) (entryEnv guard m.input) region.val initial label payload final :=
  Proofs.ret_mem_eval m guard region initial final label payload

/-- At the emitted CFG, the encoded room observation is equivalent to the
source occurrence-indexed return with the same word and whole final heap. -/
theorem ret_mem_returns (graph : Graph P.args) (m : NativeModel P) (guard : Bool)
    (initial : Heap m.cells) (word : Word) (final : Heap m.cells) :
    returnObservation initial (word, final) ∈ ssaBeh 1 (entryModel m guard) (scope graph) ↔
      graph.Returns guard m.input initial word final :=
  Proofs.ret_mem_returns graph m guard initial word final

/-- All observations of an emitted diamond in an encoded model are exactly
the encoded returns, one for each possible initial heap. -/
theorem behavior_eq_range (graph : Graph P.args) (m : NativeModel P) (guard : Bool) :
    ssaBeh 1 (entryModel m guard) (scope graph) =
      Set.range (fun initial => returnObservation initial (m.observe graph guard initial)) :=
  Proofs.behavior_eq_range graph m guard

/-- At the chosen guard, room equality compares both the word and final heap
at each initial heap. -/
theorem room_satisfaction_at (e : NativeEquation P) (m : NativeModel P) (guard : Bool) :
    (room P).Sat (Discrete.mk (entryModel m guard)) (translateEquation e) ↔
      ∀ initial, m.observe e.lhs guard initial = m.observe e.rhs guard initial :=
  Proofs.room_satisfaction_at e m guard

/-- The two guard models give exactly native satisfaction at this typed
valuation. Each room model already ranges over all initialized heaps. -/
theorem translated_satisfaction (e : NativeEquation P) (m : NativeModel P) :
    (∀ guard, (room P).Sat (Discrete.mk (entryModel m guard)) (translateEquation e)) ↔
      e.Holds m :=
  forall_congr' (fun guard => room_satisfaction_at e m guard)

/-- Re-emitting a graph after a typed entry-port map and pulling back the
entry model give the same observations, even across different scopes. -/
theorem behavior_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (m : NativeModel Q) (guard : Bool) :
    ssaBeh 1 (entryModel m guard) (scope (mapGraph h graph)) =
      ssaBeh 1 (entryModel (reduct h m) guard) (scope graph) :=
  Proofs.behavior_mapGraph h graph m guard

/-- The satisfaction square for typed entry-port maps on this image of the
lowering, at each encoded guard and valuation. -/
theorem room_satisfaction_reindex (h : P ⟶ Q) (e : NativeEquation P) (m : NativeModel Q) (guard : Bool) :
    (room Q).Sat (Discrete.mk (entryModel m guard)) (translateEquation (e.map h)) ↔
      (room P).Sat (Discrete.mk (entryModel (reduct h m) guard)) (translateEquation e) :=
  Proofs.room_satisfaction_reindex h e m guard

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution
