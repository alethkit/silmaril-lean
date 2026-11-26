module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Proofs

open Sequential
open Sequential.Flat.Serial (Code Agrees observe returns)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (carried carriedData results resultData point)
open OrderedRuntime.Structured (RuntimeValues Threaded decode)
open TwoBlock.TwoExit (Carrier ExitCode enter callCase exitLabel)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)
open NestedTheta.ExplicitRuntime.Splice (append_denote)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Z H U V M Y I J L E D : τ}
variable {ps qs ts sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private abbrev Point (X : τ) := Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried X))

private theorem repack (p : Point (σ := σ) X) :
    point (p.get .head) (p.get (.tail .head)) = p := by
  cases p with
  | cons value tail =>
    cases tail with
    | cons token tail => cases tail; rfl

private theorem at_entry (p : Code Φ A X Z L E D sigs) (input : TyDen A) (token : σ) :
    p.1.denoteOpenWith (Wires.wireModel (ε := ε)) (point (enter input) token) PUnit.unit =
      observe (ε := ε) p.1.toGraph input token := by
  rw [observe, NestedTheta.Partial.observe, NestedTheta.Term.toTerm_toGraph]

private def joinPoint (out : LabelDen [M,M] × σ) : Point (σ := σ) (Carrier M I J) :=
  point (enter (merge out.1)) out.2

private theorem connector (out : LabelDen [M,M] × σ) :
    (Flat.Numbered.connector (Φ := Φ) (I := H) (E := I) (D := J)).1.denoteOpenWith
      (Wires.wireModel (ε := ε)) (ExplicitRuntime.exitTuple (A := H) (out.1, out.2)) PUnit.unit =
      Part.some (joinPoint (I := I) (J := J) out) := by
  change (Wires.wireModel (Φ := Φ) (ε := ε)).primitive
      (.ordered (carriedData (Carrier H M M)) (carriedData (Carrier M I J)) (.effect .link))
      (ExplicitRuntime.exitTuple (A := H) (out.1, out.2)) >>= _ = _
  rw [Wires.link_boundary, Part.bind_eq_bind, Part.bind_some]
  rfl

private theorem left_entry (x : TyDen (ExitCode M M)) (token : σ) :
    (Flat.Numbered.connector (Φ := Φ) (I := Y) (E := M) (D := M)).1.denoteOpenWith
      (Wires.wireModel (ε := ε))
      (point ((TypeModel.coprodEquiv (ExitCode M M) Y).symm (.inl x)) token) PUnit.unit =
      Part.some (point (enter (A := M) (C := M) (D := M)
        (Sum.elim id id (TypeModel.coprodEquiv M M x))) token) := by
  let label := exitLabel (TypeModel.coprodEquiv M M x)
  have payload : exitPayload label = TypeModel.coprodEquiv M M x := by
    unfold label
    cases TypeModel.coprodEquiv M M x <;> rfl
  have merged : merge label = Sum.elim id id (TypeModel.coprodEquiv M M x) := by
    unfold label
    cases TypeModel.coprodEquiv M M x <;> rfl
  have packed : ExplicitRuntime.exitTuple (A := Y) (label, token) =
      point ((TypeModel.coprodEquiv (ExitCode M M) Y).symm (.inl x)) token := by
    unfold ExplicitRuntime.exitTuple TwoBlock.TwoExit.finish
    rw [payload, Equiv.symm_apply_apply]
  rw [← packed, connector (out := (label, token))]
  exact congrArg (fun value => Part.some (point (enter value) token)) merged

private theorem arm_exit (p : Code Φ A X Z H M M ps) {src : Flat.Fragment Φ A M M}
    (hp : Agrees (ε := ε) (σ := σ) src p.1.toGraph) (x : TyDen A) (token : σ) :
    (p.1.denoteOpenWith (Wires.wireModel (ε := ε)) (point (enter x) token) PUnit.unit >>= fun out =>
      (Flat.Numbered.connector (Φ := Φ) (I := H) (E := I) (D := J)).1.denoteOpenWith
        (Wires.wireModel (ε := ε)) out PUnit.unit) =
      Part.map (joinPoint (I := I) (J := J))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) src.typing (PUnit.unit, x)).run token) := by
  rw [at_entry, hp (PUnit.unit, x) token, Part.bind_eq_bind, Part.bind_map, ← Part.bind_some_eq_map]
  congr 1
  funext out
  rcases out with ⟨label, state⟩
  exact connector (label, state)

private def classify (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y)) (x : TyDen A) (token : σ) :=
  (Wires.wireModel (Φ := Φ) (ε := ε)).primitive
    (.ordered (carriedData (Carrier A X Z)) (resultData (ChoiceCarrier M Y))
      (.effect (.loop (.acyclic (.classify .right gate)))))
    (point (enter x) token)

private def gateResult (r : (TyDen (ExitCode M M) ⊕ TyDen Y) × σ) :
    Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (results (ChoiceCarrier M Y))) :=
  decode (ExplicitRuntime.choiceData r.1, r.2)

private theorem classify_eq (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y)) (x : TyDen A) (token : σ) :
    classify (X := X) (Z := Z) (ε := ε) gate x token =
      Part.map gateResult ((callCase (ε := ε) (m := StateT σ Part.{u}) gate x).run token) := by
  change Part.map decode ((match ExplicitRuntime.readRoute (.right (X := ExitCode X Z)) (enter x) with
    | some a => callCase (ε := ε) gate a >>= fun r => (pure (ExplicitRuntime.choiceData r) : StateT σ Part.{u} _)
    | none => StateT.mk fun _ => Part.none).run token) = _
  simp [ExplicitRuntime.readRoute, enter, Part.map_map, Function.comp_def]
  rfl

private theorem select_agrees (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : Code Φ M M M U M M ps) (q : Code Φ Y M M V M M qs)
    {left : Flat.Fragment Φ M M M} {right : Flat.Fragment Φ Y M M}
    (hp : Agrees (ε := ε) (σ := σ) left p.1.toGraph) (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (token : σ) :
    (Wiring.select (X := X) (Z := Z) (I := I) (J := J) gate p q).1.denoteOpenWith
        (Wires.wireModel (ε := ε)) (point (enter env.2) token) PUnit.unit =
      Part.map (joinPoint (I := I) (J := J))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Flat.fork left right gate).typing env).run token) := by
  rw [Flat.denote_fork _ _ _ coherent, StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
  unfold Wiring.select
  rw [NestedTheta.Term.denoteOpenWith, Part.bind_eq_bind]
  change (classify (X := X) (Z := Z) (ε := ε) gate env.2 token).bind _ = _
  rw [classify_eq, Part.bind_map]
  congr 1
  funext out
  rcases out with ⟨branch, state⟩
  cases branch with
  | inl x =>
    rw [NestedTheta.Term.denoteOpenWith, Part.bind_eq_bind]
    change ((Wiring.leftArm p).1.denoteOpenWith (Wires.wireModel (ε := ε))
        (point ((TypeModel.coprodEquiv (ExitCode M M) Y).symm (.inl x)) state) PUnit.unit).bind
      (fun q => Part.some (point (q.get .head) (q.get (.tail .head)))) = _
    simp only [repack (σ := σ), Part.bind_some_right, Wiring.leftArm, append_denote,
      Part.bind_eq_bind, Part.bind_assoc]
    rw [left_entry (Φ := Φ) (ε := ε), Part.bind_some]
    exact arm_exit p hp _ state
  | inr y =>
    rw [NestedTheta.Term.denoteOpenWith, Part.bind_eq_bind]
    change ((Wiring.rightArm q).1.denoteOpenWith (Wires.wireModel (ε := ε))
        (point (enter y) state) PUnit.unit).bind
      (fun q => Part.some (point (q.get .head) (q.get (.tail .head)))) = _
    simp only [repack (σ := σ), Part.bind_some_right, Wiring.rightArm, append_denote]
    exact arm_exit q hq y state

theorem branch_agrees (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : Code Φ M M M U M M ps) (q : Code Φ Y M M V M M qs) (k : Code Φ M I J L E D ts)
    {left : Flat.Fragment Φ M M M} {right : Flat.Fragment Φ Y M M} {tail : Flat.Fragment Φ M E D}
    (hp : Agrees (ε := ε) (σ := σ) left p.1.toGraph) (hq : Agrees (ε := ε) (σ := σ) right q.1.toGraph)
    (hk : Agrees (ε := ε) (σ := σ) tail k.1.toGraph)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) (Flat.link (Flat.fork left right gate) tail)
      (Wiring.branch (X := X) (Z := Z) gate p q k).1.toGraph := by
  intro env token
  simp only [observe, NestedTheta.Partial.observe, NestedTheta.Term.toTerm_toGraph, Wiring.branch]
  rw [append_denote, select_agrees gate p q hp hq coherent,
    Flat.denote_link _ _ coherent, StateT.run_bind]
  simp only [Part.bind_eq_bind, Part.bind_map, Part.map_bind]
  congr 1
  funext out
  exact (at_entry k (merge out.1) out.2).trans (hk (PUnit.unit, merge out.1) out.2)

theorem agrees (s : Syntax Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) s.source s.graph := by
  induction s with
  | loop s => exact (Flat.Serial.Spine.loop s).agrees coherent
  | link p q hp hq => exact Flat.Serial.splice_agrees p.code q.code hp hq coherent
  | branch gate p q k hp hq hk => exact branch_agrees gate p.code q.code k.code hp hq hk coherent

theorem returns_iff {src : Flat.Fragment Φ A E D} {g : Flat.Serial.Graph Φ A X Z L E D sigs}
    (h : Agrees (ε := ε) (σ := σ) src g) (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) src.typing env).run initial = Part.some (exit, final) := by
  rw [returns, ← NestedTheta.Partial.observe_eq_some]
  change observe (ε := ε) g env.2 initial = _ ↔ _
  rw [h env initial, Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  simp only [ExplicitRuntime.exitTuple_injective.eq_iff, exists_eq_right]

theorem map_none_iff {P Q : Type u} (f : P → Q) (x : Part P) :
    Part.map f x = Part.none ↔ x = Part.none := by
  rw [Part.eq_none_iff', Part.eq_none_iff']
  rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Proofs
