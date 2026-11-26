module

public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Thms

/-! The local Boolean dispatch law on RVSDG models over a lifted diamond
signature. The admissible room retains the existing RVSDG sentences and
evaluates them in the underlying model. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)

universe u v w
variable {Data : Type u} {P Q : Signature.{u, v} Data}

abbrev TargetModel (P : Signature.{u, v} Data) := RVSDG.Model.{u, max u v, w} (signature P).op

/-- Dispatch uses the native Boolean carrier and tag and forwards its two
captures in order. Either incoming Region order is allowed. -/
structure Admissible (m : TargetModel.{u, v, w} P) : Prop where
  predicate : m.value .predicate = ULift.{w} Bool
  dispatch (out : ValueSort Data) (flag : m.value .predicate)
    (captures : Tuple m.Val [RVSDG.PortType.value out, .value out]) :
    m.run (Opcode.dispatch out) (.cons flag captures) =
      .cons ⟨(Projection.ofBool (cast predicate flag).down).arm⟩ captures

abbrev AdmissibleModel (P : Signature.{u, v} Data) :=
  {m : TargetModel.{u, v, w} P // Admissible m}

theorem Admissible.value_eq {m : TargetModel.{u, v, w} P} (h : Admissible m) :
    m.value = sortValue (fun t => m.value (.data t)) :=
  funext fun | .predicate => h.predicate | .data _ => rfl

/-- Read the unique result of each target primitive after aligning carriers. -/
def extractWithCarriers (m : TargetModel.{u, v, w} P) (value : Data → Type w)
    (carriers : m.value = sortValue value) : Model.{u, v, w} P.op where
  value := value
  run {ins out} op input :=
    have state : m.state = (fun s => nomatch s) := funext fun s => nomatch s
    have ports : m.Val = Val value := congrArg₂ RVSDG.PortType.Val carriers state
    let args := cast (congrArg (fun F => Tuple F (dataPorts ins)) ports.symm) input
    cast (congrFun carriers out) ((m.run (Opcode.pure op) args).get .head)

/-- Recover the data carriers and primitive interpretations from the target. -/
def extract (m : AdmissibleModel.{u, v, w} P) : Model.{u, v, w} P.op :=
  extractWithCarriers m.val (fun t => m.val.value (.data t)) m.property.value_eq

/-- The existing sentence type and satisfaction action with admissible models. -/
def targetRoom (P : Signature.{u, v} Data) :
    Room.{max u v, max u v (w + 1), max u v (w + 1)} where
  Sen := RVSDG.Institution.Equation (signature P).op
  Mod := Cat.of (Discrete (AdmissibleModel.{u, v, w} P))
  Sat m e := e.Holds m.as.val

/-- The lifted signature map fixes dispatch and the existing reduct retains
the carriers, so admission is preserved. -/
theorem admissible_reduct (h : P ⟶ Q) {m : TargetModel.{u, v, w} Q} (law : Admissible m) :
    Admissible (RVSDG.Institution.reduct (mapOpcode h) m) :=
  ⟨law.predicate, fun out flag captures => law.dispatch out flag captures⟩

/-- Apply the actual RVSDG reduct and retain its dispatch law. -/
def reductModel (h : P ⟶ Q) (m : AdmissibleModel.{u, v, w} Q) : AdmissibleModel.{u, v, w} P :=
  ⟨RVSDG.Institution.reduct (mapOpcode h) m.val, admissible_reduct h m.property⟩

/-- Restrict the existing RVSDG corridor at the lifted signature map. -/
def targetCorridor (h : P ⟶ Q) : targetRoom.{u, v, w} P ⟶ targetRoom.{u, v, w} Q :=
  let lifted := RVSDG.Institution.corridor.{u, max u v, w} (mapSignature h)
  ⟨lifted.sen, Discrete.functor (fun m => Discrete.mk (reductModel h m)),
    fun m e => lifted.sat (Discrete.mk m.as.val) e⟩

end Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG
