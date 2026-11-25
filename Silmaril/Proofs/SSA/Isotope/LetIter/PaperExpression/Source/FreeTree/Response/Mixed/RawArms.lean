module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.RawArms.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.InstructionMap.Thms

/-! # Fixed-bound transport of atomic flattening into the mixed signature -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv HasTypeEffect)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.RawArms.Proofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {c : α}

private theorem tuple_source_map (k : Nat) (xs : Fin k → Expr Φ) :
    (sourceTuple k xs).mapInstr (Sum.inl : Φ → Φ ⊕ Ψ) =
      sourceTuple k (fun i => (xs i).mapInstr Sum.inl) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [sourceTuple, Expr.mapInstr, ih]

private theorem tree_source_map {n : Nat} {ss : Fin n → α} {a : α} (t : Tree S ss a) :
    t.source.mapInstr (Sum.inl : Φ → Φ ⊕ Ψ) = SumCall.treeSource S t := by
  induction t with
  | var i => rfl
  | op f args ih =>
    simp only [Tree.source, SumCall.treeSource, Expr.mapInstr, tuple_source_map, ih]

private theorem sequence_source_map {n : Nat} {ss : Fin n → α} (p : Sequence S c ss) :
    p.source.mapInstr (Sum.inl : Φ → Φ ⊕ Ψ) = SumCall.armSource S p := by
  induction p with
  | ret p => exact tree_source_map S p
  | call f args next ih =>
    simp only [Sequence.source, Expr.mapInstr, tree_source_map, SumCall.treeSource, SumCall.armSource, ih]

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

public theorem arm_compile_eqv (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Flatten.Program S slots c) (hp : Flatten.Program.WellTyped S e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ (.base c) e (p.source.mapInstr Sum.inl)
      (Mixed.ofSequence S T (Flatten.compile (ε := ε) S p)).source := by
  let atom := S.endpoints
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  have h := Flatten.compile_eqv S hΓ hslots e p hp
  have he := h.mapInstr (φ := (Sum.inl : Φ → Φ ⊕ Ψ)) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  simpa only [sequence_source_map, Mixed.ofSequence_source] using he

public theorem compile_typed (e : ε) (p : Program S T slots c) (hp : Program.WellTyped S T e p) :
    Mixed.Program.WellTyped S T e (Program.compile (ε := ε) S T p) :=
  ⟨hp.1, hp.2.1,
    (Mixed.ofSequence_wellTyped S T e _).mpr (Flatten.compile_typed S e p.left hp.2.2.1),
    (Mixed.ofSequence_wellTyped S T e _).mpr (Flatten.compile_typed S e p.right hp.2.2.2)⟩

omit [HasEff Φ ε] [HasEff Ψ ε] in
private theorem context_extended (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (a : α) : EffectCtx.Pure ((Ty.base a, (⊥ : ε)) :: Γ) ∧
      ∀ i : Fin (Γ.length + 1),
        (((Ty.base a, (⊥ : ε)) :: Γ).get i).1 = .base (extendSorts a slots i) :=
  ⟨fun i => Fin.cases (motive := fun j => (((Ty.base a, (⊥ : ε)) :: Γ).get j).2 = ⊥) rfl hΓ i,
    fun i => Fin.cases (motive := fun j =>
      (((Ty.base a, (⊥ : ε)) :: Γ).get j).1 = .base (extendSorts a slots j)) rfl hslots i⟩

private theorem scrutinee_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T slots c) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ (.op (.inr p.op) (sourceTuple (T.arity p.op) (fun i => SumCall.treeSource S (p.args i))))
      (SumCall.result T p.op) e := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  have hw := Mixed.source_wf S T hΓ hslots e (Program.compile (ε := ε) S T p) (compile_typed S T e p hp)
  simp only [Program.compile, Mixed.Program.source] at hw
  cases hw with
  | case he _ _ =>
    cases he with
    | op hf ha => exact .op hf ha

public theorem compile_eqv (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T slots c) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ (.base c) e p.source (Program.compile (ε := ε) S T p).source := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  obtain ⟨hl, hsl⟩ := context_extended hΓ hslots (T.left p.op)
  obtain ⟨hr, hsr⟩ := context_extended hΓ hslots (T.right p.op)
  exact .case (.refl (scrutinee_wf S T hΓ hslots e p hp))
    (arm_compile_eqv S T hl hsl e p.left hp.2.2.1) (arm_compile_eqv S T hr hsr e p.right hp.2.2.2)

variable [EffectIteration ε]

public theorem compile_native (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T slots c) (hp : Program.WellTyped S T e p)
    {t : Tm Empty (Φ ⊕ Ψ) Γ.length} (ht : p.source.toLetIter Γ.length = some t) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    HasTypeEffect Γ₀ Γ.toBoundCtx t (.base c) e ∧
    HasTypeEffect Γ₀ Γ.toBoundCtx (Program.compile (ε := ε) S T p).native (.base c) e ∧
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t (Program.compile (ε := ε) S T p).native (.base c) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  have he := compile_eqv S T hΓ hslots e p hp
  exact Eqv.toLetIter_at_bound ⟨_, he.endpoints_wf.1⟩ ⟨_, he.endpoints_wf.2⟩ he ht (Mixed.lowers S T _)

variable [DecidableEq α]

public theorem endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T slots c) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q)
    {t s : Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ht : p.source.toLetIter Γ.length = some t) (hs : q.source.toLetIter Γ.length = some s) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s (.base c) ↔ Eqv Γ (.base c) e p.source q.source := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  refine ⟨fun hn => ?_, fun he => he.toLetIter ht hs⟩
  have ep := compile_eqv S T hΓ hslots e p hp
  have eq := compile_eqv S T hΓ hslots e q hq
  have np := ep.toLetIter ht (Mixed.lowers S T _)
  have nq := eq.toLetIter hs (Mixed.lowers S T _)
  have hm := (Mixed.endpoint_reflection S T visible hΓ hslots e _ _
    (compile_typed S T e p hp) (compile_typed S T e q hq)).mp (np.symm.trans (hn.trans nq))
  exact ep.trans (hm.trans eq.symm)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.RawArms.Proofs
