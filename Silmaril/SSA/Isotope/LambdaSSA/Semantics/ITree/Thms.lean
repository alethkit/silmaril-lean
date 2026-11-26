module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.Renaming

/-! # Renaming of weak interaction-tree interpretations -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction

variable {F : Type w → Type w} {Φ : Type v} {α : Type u} (instr : Primitive F Φ α)
  {env env' : Env α} {ρ : Nat → Nat}

theorem term_rename (a : Tm Φ) (h : ∀ i, env' (ρ i) = env i) :
    term instr env' (a.rename ρ) = term instr env a :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.term_rename instr a h

theorem region_renameVars (r : Region Φ) (h : ∀ i, env' (ρ i) = env i) :
    region instr env' (r.renameVars ρ) = region instr env r :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.region_renameVars instr r h

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction
