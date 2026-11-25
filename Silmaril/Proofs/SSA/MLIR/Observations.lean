module

public import Silmaril.SSA.MLIR.Defs

public section

namespace Silmaril.Proofs.MLIR.Arith

open Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.Morphism.SSAIter (envOfBound_agrees)
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.MLIR.Arith

theorem toLambdaSSA_observations {Γ : List Width} {w : Width} (block : Block Γ w) (env : Env Γ) :
    ssaBeh 1 env.observationModel block.toScopedLambdaSSA =
      {Observation.ret () (0, word (block.denote env)) ()} := by
  have agrees : Morphism.CaseSSA.EnvAgrees env.toLambdaSSA env.toLetIter := fun _ => rfl
  have evalIff (label : Nat) (out : Value Atom) :=
    (scoped_eval_congr (instr := instr) block.toScopedLambdaSSA.property
      (envOfBound_agrees env.toLetIter) agrees (s := ()) (s' := ()) (label := label)
      (out := out)).trans (block.toLambdaSSA_eval_iff env label out)
  have run := (evalIff 0 (word (block.denote env))).mpr ⟨rfl, rfl⟩
  have det : InstrDeterministic instr := by
    intro op arg s out s' out' s'' h h'
    exact ⟨Option.some.inj (h.symm.trans h'), Subsingleton.elim _ _⟩
  ext obs
  cases obs with
  | ret s out s' =>
      change Nat × Value Atom at out
      cases s
      cases s'
      refine ret_mem_ssaBeh.trans ((evalIff out.1 out.2).trans
        (Iff.trans ?_ Set.mem_singleton_iff.symm))
      change _ ↔ Observation.ret (σ := Unit) () out () =
        Observation.ret () (0, word (block.denote env)) ()
      simp [Prod.ext_iff]
  | fault s s' =>
      constructor
      · intro h
        exact (Region.Fault.false (instr := instr) (fault_mem_ssaBeh.mp h)).elim
      · intro h
        cases Set.mem_singleton_iff.mp h
  | diverge s =>
      cases s
      constructor
      · intro h
        exact (run.not_diverges det (External.Diverges.false_iff.mp (diverge_mem_ssaBeh.mp h))).elim
      · intro h
        cases Set.mem_singleton_iff.mp h

end Silmaril.Proofs.MLIR.Arith
