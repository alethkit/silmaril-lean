module

public import Silmaril.SSA.RVSDG.Theta.Categorical.Defs
public import Silmaril.SSA.RVSDG.Theta.Thms
public import Silmaril.SSA.RVSDG.Categorical.Thms

public section

namespace Silmaril.SSA.RVSDG.Theta.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w d h c k
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

section Category

variable {D : Type d} {C : Type c} [Category.{h} D] [CartesianMonoidalCategory D]
  [Category.{k} C] [HasBinaryCoproducts C]
variable (J : D ⥤ C) [PreservesFiniteCoproducts J]

theorem route_leg (sel : Categorical.Selectors D) (X : D) (i : Fin 2) :
    J.map (Categorical.selectorLeg (sel.tag i) : X ⟶ sel.obj 2 ⊗ X) ≫ route J sel X =
      Fin.cases coprod.inl (fun _ => coprod.inr) i :=
  (isColimitOfPreserves J (sel.colimit 2 X)).fac
    (routingCocone J X) ⟨i⟩

theorem denote_toTerm [Iteration C] (m : Categorical.Model Op D) (g : Graph Op carried sigs) :
    g.toTerm.denote J m = g.denote J m := by
  unfold Term.denote Graph.denote Graph.toTerm
  rw [RVSDG.Graph.denote_toTerm]

end Category

variable (m : Model.{u, v, w} Op) (g : Graph Op carried sigs)

abbrev packed (m : Model.{u, v, w} Op) (carried : Ports (PortType V S)) :=
  Categorical.portsObj m.Val carried

noncomputable def partStep : packed m carried → _root_.Part (packed m carried ⊕ packed m carried) :=
  ((step partJ (Categorical.Model.ofRuntime m) (partJ.map (g.body.denote (Categorical.Model.ofRuntime m)))) ≫
    (Kleisli.Type.coprodIsoSum _root_.Part (partJ.obj (packed m carried)) (partJ.obj (packed m carried))).hom).of

set_option backward.isDefEq.respectTransparency false in
private theorem route_type (x : Type w) (i : Fin 2) (payload : x) :
    ((route partJ Categorical.typeSelectors x) ≫
      (Kleisli.Type.coprodIsoSum _root_.Part (partJ.obj x) (partJ.obj x)).hom).of (ULift.up i, payload) =
      _root_.Part.some (Fin.cases (.inl payload) (fun _ => .inr payload) i) := by
  let compare := (Kleisli.Type.coprodIsoSum _root_.Part (partJ.obj x) (partJ.obj x)).hom
  have evaluated (j : Fin 2) :
      ((route partJ Categorical.typeSelectors x) ≫ compare).of (ULift.up j, payload) =
        ((Fin.cases coprod.inl (fun _ => coprod.inr) j) ≫ compare).of payload := by
    have h := congrArg (fun f => (f ≫ compare).of payload)
      (route_leg partJ Categorical.typeSelectors x j)
    rw [Category.assoc] at h
    conv_lhs at h => rw [Kleisli.Type.comp_of_eq_kleisliRight]
    change (_root_.Part.some (ULift.up j, payload)).bind _ = _ at h
    rwa [_root_.Part.bind_some] at h
  apply (evaluated i).trans
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg (fun f => f.of payload)
      (Kleisli.Type.inl_coprodIsoSum_hom _root_.Part (partJ.obj x) (partJ.obj x))
  · exact congrArg (fun f => f.of payload)
      (Kleisli.Type.inr_coprodIsoSum_hom _root_.Part (partJ.obj x) (partJ.obj x))

set_option backward.isDefEq.respectTransparency false in
theorem part_step (input : Tuple m.Val carried) :
    partStep m g (Categorical.pack input) =
      match g.body.run m input with
      | .cons tag next => _root_.Part.some
          (Fin.cases (.inl (Categorical.pack next)) (fun _ => .inr (Categorical.pack next)) tag.down) := by
  unfold partStep step
  rw [Category.assoc]
  rw [Kleisli.Type.comp_of_eq_kleisliRight]
  change (_root_.Part.some (g.body.denote (Categorical.Model.ofRuntime m) (Categorical.pack input))).bind _ = _
  rw [_root_.Part.bind_some, Graph.denote_pack]
  cases g.body.run m input with
  | cons tag next =>
    rcases tag with ⟨i⟩
    exact route_type _ i (Categorical.pack next)

private theorem pack_eq {xs ys : Tuple m.Val carried} :
    Categorical.pack xs = Categorical.pack ys ↔ xs = ys :=
  ⟨fun eq => by simpa only [Categorical.unpack_pack] using congrArg (Categorical.unpack carried) eq,
    congrArg Categorical.pack⟩

set_option backward.isDefEq.respectTransparency false in
private theorem step_mem (input output : Tuple m.Val carried) (again : Bool) :
    (if again then Sum.inr (Categorical.pack output) else Sum.inl (Categorical.pack output)) ∈
      partStep m g (Categorical.pack input) ↔
    g.body.run m input = bodyResult m again output := by
  have ne : (ULift.up (0 : Fin 2) : ULift.{w} (Fin 2)) ≠ ULift.up 1 := by
    intro h
    have bad := congrArg (fun i => i.down.val) h
    cases bad
  rw [part_step]
  cases g.body.run m input with
  | cons tag next =>
    rcases tag with ⟨i⟩
    revert i
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · cases again <;> simp [bodyResult, pack_eq, ne, eq_comm]
    · simp only [Fin.cases_succ]
      have hj : j.succ = (1 : Fin 2) := congrArg Fin.succ (Fin.eq_zero j)
      rw [hj]
      cases again <;> simp [bodyResult, pack_eq, ne, eq_comm]

private theorem returns_of_runs {input output : packed m carried}
    (run : Silmaril.Elgot.Part.Runs (partStep m g) input output) :
    g.Returns m (Categorical.unpack carried input) (Categorical.unpack carried output) := by
  induction run with
  | done last =>
    apply Iterate.stop
    apply (step_mem m g _ _ false).mp
    simpa [Categorical.pack_unpack] using last
  | more step rest ih =>
    apply Iterate.again _ ih
    apply (step_mem m g _ _ true).mp
    simpa [Categorical.pack_unpack] using step

private theorem runs_of_returns {input output : Tuple m.Val carried}
    (run : g.Returns m input output) :
    Silmaril.Elgot.Part.Runs (partStep m g) (Categorical.pack input) (Categorical.pack output) := by
  induction run with
  | stop last => exact .done ((step_mem m g _ _ false).mpr last)
  | again step rest ih => exact .more ((step_mem m g _ _ true).mpr step) ih

theorem mem_denote (input output : Tuple m.Val carried) :
    Categorical.pack output ∈ g.denotePart m input ↔
    g.Returns m input output := by
  change Categorical.pack output ∈ Silmaril.Elgot.iter (partStep m g) (Categorical.pack input) ↔ _
  rw [Silmaril.Elgot.Part.mem_iter_iff]
  exact ⟨fun run => by
    simpa only [Categorical.unpack_pack] using returns_of_runs m g run,
    runs_of_returns m g⟩

private def next (input : Tuple m.Val carried) : Tuple m.Val carried :=
  match g.body.run m input with
  | .cons _ output => output

private theorem next_continues (input : Tuple m.Val carried) (never : ∀ output, ¬g.Returns m input output) :
    g.body.run m input = bodyResult m true (next m g input) := by
  unfold next
  generalize h : g.body.run m input = result
  cases result with
  | cons tag output =>
    rcases tag with ⟨i⟩
    revert h
    refine Fin.cases ?_ (fun j => ?_) i
    · intro he
      exact (never output (.stop he)).elim
    · rw [Fin.eq_zero j]
      intro _
      rfl

theorem diverges_iff_no_return (input : Tuple m.Val carried) :
    g.Diverges m input ↔ ∀ output, ¬g.Returns m input output := by
  constructor
  · exact fun hd _ hr => Graph.not_diverges_of_returns g m hr hd
  · intro h
    let trace : Nat → Tuple m.Val carried := fun n => (next m g)^[n] input
    have hs (n : Nat) : trace (n + 1) = next m g (trace n) :=
      Function.iterate_succ_apply' _ _ _
    have none (n : Nat) : ∀ output, ¬g.Returns m (trace n) output := by
      induction n with
      | zero => exact h
      | succ n ih =>
        intro output run
        rw [hs n] at run
        exact ih output (.again (next_continues m g (trace n) ih) run)
    exact ⟨trace, rfl, fun n => by rw [hs]; exact next_continues m g (trace n) (none n)⟩

theorem denote_none_iff (input : Tuple m.Val carried) :
    g.denotePart m input = _root_.Part.none ↔
    g.Diverges m input := by
  change Silmaril.Elgot.iter (partStep m g) (Categorical.pack input) = _root_.Part.none ↔ _
  rw [_root_.Part.eq_none_iff, diverges_iff_no_return]
  constructor
  · exact fun h output run => h _ ((mem_denote m g input output).mpr run)
  · intro h output member
    let tuple : Tuple m.Val carried := Categorical.unpack carried output
    have eq : Categorical.pack tuple = output := Categorical.pack_unpack carried output
    rw [← eq] at member
    exact h _ ((mem_denote m g input tuple).mp member)

end Silmaril.SSA.RVSDG.Theta.Proofs
