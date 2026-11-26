module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Obstruction.Thms

/-! Substitution into descended native classes can reach UB on one branch,
bypass an unreachable UB, and preserve infinite replay below UB. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA (VCtx LCtx)
open Silmaril.Isotope.LambdaSSA.Region (CfgQuotient CfgEquiv TypedRegion cfgSetoid)
open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.Morphism.SSAIter (envOfBound)

namespace LambdaSSAUBNativeQuotientRegression

private abbrev τ := Ty Empty
private abbrev Γ : VCtx τ := []
private abbrev L : LCtx τ := [unit, unit]
private abbrev K : LCtx τ := [unit]

local instance : HasTy Unit τ := ⟨fun _ => unit, fun _ => coprod unit unit⟩

private abbrev choices : Model Unit 0 where
  α := Unit
  σ := Unit
  instr _ _ _ out _ := out = .inl .unit ∨ out = .inr .unit
  faults _ _ _ _ := False
  prim _ _ _ := False
  bound := Fin.elim0

private abbrev idle : Model Unit 0 where
  α := Unit
  σ := Unit
  instr _ _ _ _ _ := False
  faults _ _ _ _ := False
  prim _ _ _ := False
  bound := Fin.elim0

private def cfgClass (r : TypedRegion (Φ := Unit) Γ L) : CfgQuotient (Φ := Unit) Γ L :=
  Quotient.mk (cfgSetoid Γ L) r

private def zero (r : TypedRegion (Φ := Unit) Γ L) : TypedRegion (Φ := Unit) Γ L :=
  ⟨.cfg r.val 0 Fin.elim0, .cfg (fun i => Fin.elim0 i) r.property (fun i => Fin.elim0 i)⟩

private theorem zero_class (r : TypedRegion (Φ := Unit) Γ L) : cfgClass (zero r) = cfgClass r :=
  Quotient.sound (.cfgZero r.property Fin.elim0)

private def k (i : Fin L.length) : Region Unit (L.get i :: Γ) K :=
  if i.val = 0 then .ub else .native ⟨.br 0 .unit, .br rfl .unit⟩

private def nondeterministic : TypedRegion (Φ := Unit) Γ L :=
  ⟨.case (.op () .unit) (.br 0 .unit) (.br 1 .unit),
    .case (.op (f := ()) .unit) (.br (ℓ := 0) rfl .unit) (.br (ℓ := 1) rfl .unit)⟩

theorem one_path_ub :
    Outcome.ret (0 : Fin 2) .unit () ∈ (nativeDenotation nondeterministic choices ()).possible ∧
    Outcome.ret (1 : Fin 2) .unit () ∈ (nativeDenotation nondeterministic choices ()).possible ∧
    substCfg (cfgClass (zero nondeterministic)) k choices () =
      substCfg (cfgClass nondeterministic) k choices () ∧
    substCfg (cfgClass nondeterministic) k choices () = ⊤ := by
  have reachesLeft : Outcome.ret (0 : Fin 2) .unit () ∈
      (nativeDenotation nondeterministic choices ()).possible :=
    LambdaSSA.Semantics.Region.Eval.case_inl (.op .unit (Or.inl rfl)) (.br .unit)
  refine ⟨reachesLeft, LambdaSSA.Semantics.Region.Eval.case_inr (.op .unit (Or.inr rfl)) (.br .unit),
    congrArg (fun q => substCfg q k choices ()) (zero_class nondeterministic), ?_⟩
  exact Behaviour.bind_eq_top_of_reaches_top reachesLeft rfl

private def bypass : TypedRegion (Φ := Unit) Γ L :=
  ⟨.br 1 .unit, .br rfl .unit⟩

private def bypassEntry : TypedRegion (Φ := Unit) Γ (L ++ L) :=
  ⟨.br 3 .unit, .br rfl .unit⟩

-- If entered, either local block would select the UB continuation at exit zero.
private def bypassBlocks (i : Fin L.length) : TypedRegion (Φ := Unit) (L.get i :: Γ) (L ++ L) :=
  ⟨.br 2 .unit, .br rfl .unit⟩

private def bypassCfg : TypedRegion (Φ := Unit) Γ L :=
  cfgRepresentative bypassEntry bypassBlocks

private theorem bypass_class : cfgClass bypassCfg = cfgClass bypass :=
  Quotient.sound (.cfgBrExit (ℓ := 1) (fun _ : Fin 2 => unit) rfl .unit
    (fun _ => .br (ℓ := 2) rfl .unit))

private abbrev bypassEntryClass :=
  Quotient.mk (cfgSetoid Γ (L ++ L)) bypassEntry

private abbrev bypassBlockClass (i : Fin L.length) :=
  Quotient.mk (cfgSetoid (L.get i :: Γ) (L ++ L)) (bypassBlocks i)

private noncomputable abbrev bypassGraph :=
  cfgRun (R := L) (L := L) bypassEntryClass bypassBlockClass idle

private def insideFirst : Feedback.Point L.length Unit Unit → Prop
  | .entry _ => False
  | .block i _ _ => i.val = 0

theorem outward_staged :
    ((Feedback.Graph.ofRun
      (Feedback.relabel (S := L) (Equiv.swap (0 : Fin 2) 1) bypassGraph)).outer insideFirst).close
        (.entry ()) = cfgDenotation (cfgClass bypass) idle () :=
  (cfgRun_relabel_staged (R := L) (S := L) (L := L) bypassEntryClass bypassBlockClass idle ()
    (Equiv.swap (0 : Fin 2) 1) insideFirst).trans
    ((cfgDenotation_feedback_mk (R := L) (L := L) bypassEntry bypassBlocks idle ()).symm.trans
      (congrArg (fun q => cfgDenotation q idle ()) bypass_class))

theorem unreachable_ub :
    substCfg (cfgClass bypassCfg) k idle () = substCfg (cfgClass bypass) k idle () ∧
      (substCfg (cfgClass bypass) k idle ()).Ordinary (.ret 0 .unit ()) := by
  refine ⟨congrArg (fun q => substCfg q k idle ()) bypass_class, ?_⟩
  classical
  unfold substCfg Behaviour.bind
  rw [ite_eq_right]
  · exact ⟨WithTop.coe_ne_top, Or.inr ⟨1, .unit, (),
      LambdaSSA.Semantics.Region.Eval.br .unit, LambdaSSA.Semantics.Region.Eval.br .unit⟩⟩
  · rintro (top | ⟨i, a, mid, reached, top⟩)
    · exact WithTop.coe_ne_top top
    · change LambdaSSA.Semantics.Region.Eval idle.instr (envOfBound idle.bound)
        (.br 1 .unit) () i.val a mid at reached
      have label : i.val = 1 := by
        generalize i.val = label at reached
        cases reached
        rfl
      simp only [k, label, Nat.one_ne_zero, ↓reduceIte] at top
      exact WithTop.coe_ne_top top

private def loopBlock : LambdaSSA.Region Unit := .br 0 (.var 0)

private def loop : TypedRegion (Φ := Unit) Γ L :=
  ⟨.cfg (.br 0 .unit) 1 (fun _ => loopBlock),
    .cfg (fun _ : Fin 1 => unit) (.br (ℓ := 0) rfl .unit)
      (fun _ => .br (ℓ := 0) rfl (.var (i := 0) rfl))⟩

private def unfolded : TypedRegion (Φ := Unit) Γ L :=
  ⟨.cfg (.let₁ .unit loopBlock) 1 (fun _ => loopBlock),
    .cfg (fun _ : Fin 1 => unit) (.let₁ .unit (.br (ℓ := 0) rfl (.var (i := 0) rfl)))
      (fun _ => .br (ℓ := 0) rfl (.var (i := 0) rfl))⟩

private theorem loop_class : cfgClass loop = cfgClass unfolded :=
  Quotient.sound (.cfgBrLocal (fun _ : Fin 1 => unit) 0 .unit
    (fun _ => .br (ℓ := 0) rfl (.var (i := 0) rfl)))

theorem infinite_replay_below_ub :
    substCfg (cfgClass loop) k idle () = substCfg (cfgClass unfolded) k idle () ∧
      (substCfg (cfgClass loop) k idle ()).Ordinary .diverge := by
  refine ⟨congrArg (fun q => substCfg q k idle ()) loop_class, ?_⟩
  have diverges := LambdaSSA.Semantics.cfg_self_loop (instr := idle.instr) (envOfBound idle.bound) ()
  have det : LambdaSSA.Semantics.InstrDeterministic idle.instr := by
    intro _ _ _ _ _ _ _ noStep
    exact noStep.elim
  classical
  unfold substCfg Behaviour.bind
  rw [ite_eq_right]
  · exact ⟨WithTop.coe_ne_top, Or.inl (LambdaSSA.Semantics.External.Diverges.of_internal diverges)⟩
  · rintro (top | ⟨i, a, mid, reached, _⟩)
    · exact WithTop.coe_ne_top top
    · exact (show LambdaSSA.Semantics.Region.Eval idle.instr (envOfBound idle.bound)
          loop.val () i.val a mid from reached).not_diverges det diverges

#print axioms cfgEquiv_obs
#print axioms cfgDenotation
#print axioms cfgDenotation_feedback_mk
#print axioms cfgRun_relabel_staged
#print axioms not_paper_family_descent
#print axioms not_continuation_family_descent
#print axioms one_path_ub
#print axioms outward_staged
#print axioms unreachable_ub
#print axioms infinite_replay_below_ub

end LambdaSSAUBNativeQuotientRegression
