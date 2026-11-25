module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
public import Silmaril.Logic.Institution.Borrowing
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.Stateless.State
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.Stateless.Reindex

/-! # Stateless reindexing and conservative inclusion at empty effects -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless

open CategoryTheory Silmaril.Logic.Institution
open OrderedRuntime.Structured (Values Ty)
open RVSDG.Institution (OpcodeMap)

universe u v w
variable {V : Type u} {A B C : Signature.{u,v} V} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

theorem noState_map (f : OpcodeMap A.op B.op) (t : Term A.op args past sigs outs) :
    NoState (Institution.mapTerm f t) ↔ NoState t :=
  Proofs.noState_map f t

theorem noState_mapGraph (f : OpcodeMap A.op B.op) (g : Graph A.op args past sigs outs) :
    NoState (Institution.mapGraph f g).toTerm ↔ NoState g.toTerm := by
  unfold Institution.mapGraph
  rw [Term.toTerm_toGraph, noState_map]

@[expose] def Equation.map (f : A ⟶ B) (e : Equation A) : Equation B :=
  ⟨Institution.Partial.Equation.map f e.val,
    (noState_mapGraph _ e.val.lhs).mpr e.property.1,
    (noState_mapGraph _ e.val.rhs).mpr e.property.2⟩

theorem observe_map (f : A ⟶ B) (m : Model.{u,v,w} B) (g : Graph A.op args [] sigs outs)
    (input : Tuple (Values m.value) args) :
    observe m (Institution.mapGraph (Institution.Partial.Signature.Hom.opcodeMap f) g) input =
      observe (reduct f m) g input :=
  Proofs.observe_map f m g input

theorem Equation.satisfaction (f : A ⟶ B) (e : Equation A) (m : Model.{u,v,w} B) :
    (e.map f).Holds m ↔ e.Holds (reduct f m) := by
  change (∀ input,
      observe m (Institution.mapGraph (Institution.Partial.Signature.Hom.opcodeMap f) e.val.lhs) input =
      observe m (Institution.mapGraph (Institution.Partial.Signature.Hom.opcodeMap f) e.val.rhs) input) ↔ _
  simp only [observe_map, Equation.Holds]
  rfl

theorem Equation.map_id (e : Equation A) : e.map (𝟙 A) = e :=
  Subtype.ext (Institution.Partial.Equation.map_id e.val)

theorem Equation.map_comp (f : A ⟶ B) (g : B ⟶ C) (e : Equation A) :
    e.map (f ≫ g) = (e.map f).map g :=
  Subtype.ext (Institution.Partial.Equation.map_comp f g e.val)

@[expose] def corridor (f : A ⟶ B) : room.{u,v,w} A ⟶ room.{u,v,w} B :=
  ⟨Equation.map f, reductFunctor f, fun m e => e.satisfaction f m.as⟩

theorem corridor_id (A : Signature.{u,v} V) : corridor (𝟙 A) = 𝟙 (room.{u,v,w} A) :=
  Room.hom_ext (funext Equation.map_id) (Discrete.functor_ext fun m => by cases m; rfl)

theorem corridor_comp (f : A ⟶ B) (g : B ⟶ C) :
    corridor.{u,v,w} (f ≫ g) = corridor f ≫ corridor g :=
  Room.hom_ext (funext (Equation.map_comp f g)) (Discrete.functor_ext fun _ => rfl)

@[expose] def inst (V : Type u) :
    Inst.{max u (v + 1), max u v, max u v, max (u + 1) v (w + 1), max (u + 1) v (w + 1)} where
  Sign := Signature.{u,v} V
  I := { obj := room.{u,v,w}, map := corridor, map_id := corridor_id, map_comp := corridor_comp }

/-- The image is the very same numbered equation, with only its admission
proof forgotten. Thus this is an injection of sentences as data. -/
def sentenceInclusion (A : Signature.{u,v} V) : Equation A ↪ Institution.Partial.Equation A.ordered :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The stateless reading observes exactly the tuples of finite nested executions. -/
theorem observe_eq_some (m : Model.{u,v,w} A) (g : Graph A.op args [] sigs outs)
    (input : Tuple (Values m.value) args) (output : Tuple (Values m.value) outs) :
    observe m g input = Part.some output ↔ NestedTheta.Partial.returns m.partial g input output :=
  NestedTheta.Partial.observe_eq_some m.partial g input output

theorem observe_forget (m : Institution.Partial.Model.{u,v,w} A.ordered σ)
    (g : Graph A.op args [] sigs outs) (input : Tuple (Values m.value) args) (initial : σ) :
    OrderedState.Partial.observe m g input initial =
      Part.map (fun output => (output, initial)) (observe (forgetStore m) g input) :=
  Proofs.observe_forget m g input initial

theorem returns_iff (m : Institution.Partial.Model.{u,v,w} A.ordered σ)
    (g : Graph A.op args [] sigs outs) (input : Tuple (Values m.value) args)
    (initial final : σ) (output : Tuple (Values m.value) outs) :
    (output, final) ∈ OrderedState.Partial.observe m g input initial ↔
      output ∈ observe (forgetStore m) g input ∧ final = initial :=
  Proofs.returns_iff m g input initial final output

theorem no_block (m : Institution.Partial.Model.{u,v,w} A.ordered σ)
    (g : Graph A.op args [] sigs outs) (input : Tuple (Values m.value) args) (initial : σ) :
    ¬ ∃ attempt, OrderedState.Partial.abnormal m g input initial (.blocked attempt) :=
  fun ⟨attempt, _⟩ => PEmpty.elim attempt.opcode

theorem diverges_iff (m : Institution.Partial.Model.{u,v,w} A.ordered σ)
    (g : Graph A.op args [] sigs outs) (input : Tuple (Values m.value) args) (initial : σ) :
    OrderedState.Partial.abnormal m g input initial .diverges ↔ Diverges (forgetStore m) g input :=
  Proofs.diverges_iff m g input initial

/-- A nonempty store allows reflection by choosing one initial store.
The forward observations hold uniformly at every initial store. -/
theorem included_holds [Nonempty σ] (e : Equation A) (m : Institution.Partial.Model.{u,v,w} A.ordered σ) :
    Institution.Partial.Equation.Holds (sentenceInclusion A e) m ↔ e.Holds (forgetStore m) :=
  Proofs.included_holds e m

@[expose] def inclusionCorridor (A : Signature.{u,v} V) (σ : Type (max u w)) [Nonempty σ] :
    room.{u,v,w} A ⟶ Institution.Partial.room A.ordered σ :=
  ⟨sentenceInclusion A, forgetFunctor A σ, fun m e => included_holds e m.as⟩

theorem inclusion_natural [Nonempty σ] (f : A ⟶ B) :
    corridor f ≫ inclusionCorridor B σ =
      inclusionCorridor A σ ≫ Institution.Partial.corridor f :=
  Room.hom_ext rfl (Discrete.functor_ext fun _ => rfl)

@[expose] def inclusion (V : Type u) (σ : Type (max u w)) [Nonempty σ] :
    Inst.CoHom (inst.{u,v,w} V) (Institution.Partial.inst.{u,v,w} V σ) where
  Φ := signatureInclusion V
  ρ := { app := fun A => inclusionCorridor A σ, naturality := fun {X Y} f => inclusion_natural (A := X) (B := Y) f }

theorem inclusion_expansive (V : Type u) (σ : Type (max u w)) [Nonempty σ] :
    (inclusion.{u,v,w} V σ).ModelExpansive :=
  fun _ m => ⟨Discrete.mk (expand m.as), rfl⟩

theorem entails_iff [Nonempty σ] (Γ : Set (Equation A)) (e : Equation A) :
    (room.{u,v,w} A).Entails Γ e ↔
      (Institution.Partial.room A.ordered σ).Entails (sentenceInclusion A '' Γ) (sentenceInclusion A e) :=
  Inst.CoHom.entails_iff (inclusion V σ) (inclusion_expansive V σ) A Γ e

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless
