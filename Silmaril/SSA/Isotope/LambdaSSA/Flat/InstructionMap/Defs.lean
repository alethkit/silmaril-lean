module

public import Silmaril.SSA.Isotope.LambdaSSA.Flat.Thms
public import Silmaril.SSA.Isotope.Bridge.CaseSSA.Thms

/-! # Primitive relabelling of scoped flat tables -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA

universe u v

variable {Φ : Type u} {Ψ : Type v}

/-- Relabel primitive occurrences while retaining all value and label indices. -/
def Flat.mapInstr {labels : Nat} (f : Φ → Ψ) : {n : Nat} → Flat Φ labels n → Flat Ψ labels n
  | _, .br i a => .br i (a.mapInstr f)
  | _, .let₁ a b => .let₁ (a.mapInstr f) (b.mapInstr f)
  | _, .let₂ a b => .let₂ (a.mapInstr f) (b.mapInstr f)
  | _, .case a l r => .case (a.mapInstr f) (l.mapInstr f) (r.mapInstr f)

/-- Map the written entry and every block at its original table index. -/
def FiniteCFG.mapInstr {blocks exits captured : Nat} (f : Φ → Ψ)
    (g : FiniteCFG Φ blocks exits captured) : FiniteCFG Ψ blocks exits captured :=
  ⟨g.entry.mapInstr f, fun i => (g.block i).mapInstr f⟩

end Silmaril.Isotope.LambdaSSA
