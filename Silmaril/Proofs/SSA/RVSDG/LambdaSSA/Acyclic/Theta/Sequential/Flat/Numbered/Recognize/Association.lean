module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Defs

/-! # Right-associating a body keeps its numbered lowering -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Proofs

open ExplicitRuntime.Wiring (Tail emit)
open OrderedRuntime.Structured (Data Threaded runtime)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A I B K M C J E D S : τ}

private def appendSeq : {A B C : τ} → Body Φ A B → Body Φ B C → Body Φ A C
  | _, _, _, .instruction op, last => .sequence (.instruction op) last
  | _, _, _, .sequence first rest, last => .sequence first (appendSeq rest last)
  | _, _, _, .choice op left right, last => .sequence (.choice op left right) last

private def normalize : {A B : τ} → Body Φ A B → Body Φ A B
  | _, _, .instruction op => .instruction op
  | _, _, .sequence first rest => appendSeq (normalize first) (normalize rest)
  | _, _, .choice op left right => .choice op (normalize left) (normalize right)

private theorem append_form {first : Body Φ A B} {last : Body Φ B C}
    (hf : RightAssociated first) (hl : RightAssociated last) : RightAssociated (appendSeq first last) := by
  induction hf with
  | instruction op => exact .thenInstruction op hl
  | choice op left right => exact .thenChoice op left right hl
  | thenInstruction op _ ih => exact .thenInstruction op (ih hl)
  | thenChoice op left right _ _ _ ih => exact .thenChoice op left right (ih hl)

private theorem normalize_form (b : Body Φ A B) : RightAssociated (normalize b) := by
  induction b with
  | instruction op => exact .instruction op
  | sequence _ _ first rest => exact append_form first rest
  | choice op _ _ left right => exact .choice op left right

variable {args outs : Ports (OrderedRuntime.Structured.Ty τ)} {past : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {a : Data args} {o : Data outs} {live : Origin (Threaded args) past runtime}

private theorem emit_append (first : Body Φ A B) (last : Body Φ B C) (route : Input S A)
    (source : Origin (Threaded args) past (.value S)) (next : Tail Φ a o C) :
    emit (appendSeq first last) route live source next = emit (.sequence first last) route live source next := by
  induction first generalizing args outs past S with
  | instruction => rfl
  | choice => rfl
  | sequence left right ihL ihR =>
    simp only [appendSeq, emit, ihR]

private theorem emit_normalize (body : Body Φ A B) (route : Input S A)
    (source : Origin (Threaded args) past (.value S)) (next : Tail Φ a o B) :
    emit (normalize body) route live source next = emit body route live source next := by
  induction body generalizing args outs past S with
  | instruction => rfl
  | sequence left right ihL ihR => simp only [normalize, emit_append, emit, ihL, ihR]
  | choice op l r ihL ihR => simp only [normalize, emit, ihL, ihR]

private def normalizeLoop (s : Loop Φ A B K E D) : Loop Φ A B K E D :=
  { s with body := normalize s.body }

private theorem loop_code (s : Loop Φ A B K E D) :
    ExplicitRuntime.Wiring.loop (normalizeLoop s) = ExplicitRuntime.Wiring.loop s := by
  have body : ExplicitRuntime.Wiring.thetaBody (normalizeLoop s) = ExplicitRuntime.Wiring.thetaBody s := by
    simp only [ExplicitRuntime.Wiring.thetaBody, ExplicitRuntime.Wiring.bodyArm, normalizeLoop, emit_normalize]
  unfold ExplicitRuntime.Wiring.loop
  rw [body]

private theorem guarded_code (p : Conditional.Guarded Φ A I B K M M) :
    Conditional.Wiring.code { p with loop := normalizeLoop p.loop } = Conditional.Wiring.code p := by
  simp only [Conditional.Wiring.code, Conditional.Wiring.openCode, Conditional.Wiring.arm]
  rw [loop_code p.loop]

theorem compile_associated (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D) :
    ∃ (p' : Conditional.Guarded Φ A I B K M M) (q' : Loop Φ M C J E D),
      RightAssociated p'.loop.body ∧ RightAssociated q'.body ∧ compile p' q' = compile p q := by
  refine ⟨{ p with loop := normalizeLoop p.loop }, normalizeLoop q,
    normalize_form _, normalize_form _, ?_⟩
  unfold compile
  rw [guarded_code, loop_code]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Proofs
