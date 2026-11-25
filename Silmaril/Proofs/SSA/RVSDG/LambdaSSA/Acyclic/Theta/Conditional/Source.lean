module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open LinearChain (Site)
open TwoBlock.TwoExit (callCase ExitCode exitLabel)
open Silmaril.Elgot (Iterate LawfulElgotMonad)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A L B K E D X Y : τ} {Γ Labels : List τ}

private def siteValue (site : Site Labels X) : TyDen X → LabelDen Labels :=
  LabelValue.inject site.index site.typing

omit [Iterate m] [LawfulElgotMonad m] in
private theorem call_denotes (op : TwoBlock.Instruction Φ X Y) :
    Denotes (m := m) ε (op.typing Γ) (fun env => TwoBlock.call (ε := ε) op env.2) := by
  obtain ⟨op, source, target⟩ := op
  subst X
  subst Y
  have d := Denotes.op (m := m) (ε := ε)
    (Denotes.var (Φ := Φ) (Γ := instrSrc op :: Γ) (i := 0) rfl)
  simpa [TwoBlock.call, Env.get, bind_pure] using d

omit [LawfulElgotMonad m] in
private theorem branch_denotes (target : Site Labels X) :
    RegionDenotes (m := m) ε (.br target.typing (.var (Φ := Φ) (Γ := X :: Γ) (i := 0) rfl))
      (fun env => pure (siteValue target env.2)) := by
  simpa only [siteValue, Env.get, pure_bind, labelInject_eq_recursive] using
    RegionDenotes.br (m := m) (ε := ε) (h := target.typing)
      (Denotes.var (Φ := Φ) (Γ := X :: Γ) (i := 0) rfl)

variable (s : Guarded Φ A L B K E D)

private def entryAction (env : Env [A]) : m (LabelDen (Theta.Labels s.loop)) :=
  callCase (ε := ε) s.gate env.2 >>= fun
    | .inl exited => pure (Sum.elim (siteValue (firstExit s)) (siteValue (secondExit s))
        (TypeModel.coprodEquiv E D exited))
    | .inr entered => pure (siteValue (enterLoop s) entered)

omit [LawfulElgotMonad m] in
private theorem entry_denotes :
    RegionDenotes (m := m) ε (entryTyping s) (entryAction (ε := ε) (m := m) s) := by
  have direct := RegionDenotes.case
    (Denotes.var (m := m) (ε := ε) (Φ := Φ) (Γ := [ExitCode E D, A]) (i := 0) rfl)
    (branch_denotes (m := m) (ε := ε) (Φ := Φ) (Γ := [ExitCode E D, A]) (firstExit s))
    (branch_denotes (m := m) (ε := ε) (Φ := Φ) (Γ := [ExitCode E D, A]) (secondExit s))
  have den := RegionDenotes.case (call_denotes (m := m) (Γ := []) s.gate) direct
    (branch_denotes (m := m) (ε := ε) (Φ := Φ) (Γ := [A]) (enterLoop s))
  convert den using 1 <;> try rfl
  funext env
  simp only [entryAction, callCase, bind_assoc, pure_bind, Env.get]
  congr 1
  funext output
  cases TypeModel.coprodEquiv (ExitCode E D) L output with
  | inr => rfl
  | inl result =>
    change (pure (Sum.elim (siteValue (firstExit s)) (siteValue (secondExit s))
      (TypeModel.coprodEquiv E D result)) : m (LabelDen (Theta.Labels s.loop))) =
      (match TypeModel.coprodEquiv E D result with
      | .inl e => pure (siteValue (firstExit s) e)
      | .inr d => pure (siteValue (secondExit s) d))
    cases TypeModel.coprodEquiv E D result <;> rfl

omit [Iterate m] [LawfulElgotMonad m] in
private theorem entry_split (env : Env [A]) :
    (entryAction (ε := ε) (m := m) s env >>= fun x => pure (LabelValue.appendSplit _ _ x)) =
      (gateAction (ε := ε) (m := m) s env.2 >>= fun branch => pure (Sequential.splitEntry s.loop branch)) := by
  simp only [entryAction, gateAction, bind_assoc, pure_bind]
  congr 1
  funext result
  cases result with
  | inr =>
    simp only [pure_bind, Sum.map_inr]
    rfl
  | inl exited =>
    simp only [pure_bind, Sum.map_inl, Sequential.splitEntry, Function.comp_apply]
    cases TypeModel.coprodEquiv E D exited with
    | inl x =>
      exact congrArg pure (Sequential.split_external [E,D] (List.ofFn (Theta.localTypes s.loop))
        0 (firstExit s).typing rfl x)
    | inr x =>
      exact congrArg pure (Sequential.split_external [E,D] (List.ofFn (Theta.localTypes s.loop))
        1 (secondExit s).typing rfl x)

theorem region_gate
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (regionTyping s) env =
      gateAction (ε := ε) s env.2 >>= fun
        | .inl external => pure external
        | .inr header => Region.denote (ε := ε) (m := m) (Theta.regionTyping s.loop) (PUnit.unit, header) :=
  Sequential.region_entry s.loop (entryTyping s) (entry_denotes s) (fun x => gateAction (ε := ε) s x.2)
    (entry_split s) coherent env

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Proofs
