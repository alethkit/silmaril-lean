module

public import Silmaril.SSA.Peggy.SimpleValidation.Defs
public import Silmaril.SSA.Peggy.Optimizer.Contextual.Thms
public import Silmaril.SSA.PEG.Simple.Revert.Thms

public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Proofs

open Bridge.Egg (model)
open Bridge.Figure11 (toAcyclic)
open RVSDG (Tuple)

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params : List (PEG.Ty Data)} {result : PEG.Ty Data}
variable {p : PEG.Simple.Program P false params result} {rules : List (Optimizer.Contextual.Schema P)}

theorem frontendRank_valid (p : PEG.Simple.Program P false params result) :
    (Acyclic.Ranked.check p.translate frontendRank).isSome = true := by
  have ordered (i : Fin p.lower.nodes.length) (j : Fin (p.translate.node i).inputs.length) :
      frontendRank ((p.translate.node i).arg j).id < frontendRank i := by
    have forward := p.lower.code.toGraph_edge_forward p.lower.refs
      (a := i) (b := ((p.translate.node i).arg j).id) (kind := (p.translate.node i).label.kind j)
      ⟨j, rfl, rfl⟩
    unfold frontendRank
    have bounded := i.isLt
    omega
  simp [Acyclic.Ranked.check, ordered]

theorem returns (accepted : Accepted p rules) (m : PEG.Interpretation.{0,0,0} P)
    (laws : ∀ rule ∈ rules.map Optimizer.Contextual.core, rule.Holds (model (toAcyclic m)))
    (input : Tuple m.Value params) {value : m.Value result} (run : p.Returns m input value) :
    accepted.output.Returns m input value := by
  have source := p.translate_returns m input run PEG.Simple.Index.zero
  have optimized := accepted.candidate.sound m laws input PEG.Simple.Index.zero
  exact accepted.schedule.revert_returns m input PEG.Simple.Index.zero (optimized.symm.trans source)

end Silmaril.SSA.Peggy.SimpleValidation.Proofs
