module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Codes
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments (case_eqv_bind)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Proofs

variable {Q K S T B : Code} {ε : Type} [HasEff (Opcode Q K) ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx (Ty Unit) ε} {e : ε}

local notation "Ops" => Opcode Q K
local notation "slot[" c "]" => (Code.ty c, (⊥ : ε))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem replies_wf (L : Table Q K S B) (s : S.Value) :
    Wf (slot[K] :: Γ)
      (K.dispatch (fun r => (Code.sum B S).literal (L.reply s r)) (.var 0) : Expr Ops)
      (Code.sum B S).ty e :=
  dispatch_wf K (fun _ => literal_wf _ _) (.var 0 bot_le)

theorem row_wf (L : Table Q K S B) (s : S.Value) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Wf Γ (L.row s) (Code.sum B S).ty e :=
  .let₁ (.op hf (literal_wf _ _)) (replies_wf L s)

theorem step_wf (L : Table Q K S B) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Wf [slot[S]] L.source (Code.sum B S).ty e :=
  dispatch_wf S (fun s => row_wf L s hf) (.var 0 bot_le)

theorem map_wf (h : S.Value → T.Value) :
    Wf (slot[S] :: Γ) (stateMap S T h : Expr Ops) T.ty e :=
  dispatch_wf S (fun _ => literal_wf _ _) (.var 0 bot_le)

theorem map_readback (h : S.Value → T.Value) (s : S.Value) :
    Eqv Γ T.ty e ((stateMap S T h : Expr Ops).subst (S.literal s).subst0) (T.literal (h s)) := by
  unfold stateMap
  rw [dispatch_subst S (fun v => literal_subst T (h v))]
  exact dispatch_beta S s (fun v => literal_subst T (h v)) (fun _ => literal_wf _ _)

omit [HasEff (Opcode Q K) ε] [Preorder ε] [OrderBot ε] in
theorem row_closed (L : Table Q K S B) (s : S.Value) (σ : Nat → Expr Ops) :
    (L.row s).subst σ = L.row s := by
  simp only [Table.row, Expr.subst]
  rw [literal_subst Q (L.request s) σ,
    dispatch_subst K (rows := fun r => (Code.sum B S).literal (L.reply s r)) (fun v => literal_subst _ _)]
  rfl

theorem step_readback (L : Table Q K S B) (s : S.Value) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Eqv ([] : EffectCtx (Ty Unit) ε) (Code.sum B S).ty e
      (L.source.subst (S.literal s).subst0) (L.row s) := by
  unfold Table.source
  rw [dispatch_subst S (row_closed L)]
  exact dispatch_beta S s (row_closed L) (fun v => row_wf L v hf)

omit [HasEff (Opcode Q K) ε] [Preorder ε] [OrderBot ε] in
theorem map_wk1 {h : S.Value → T.Value} :
    (stateMap S T h : Expr Ops).wk1 = stateMap S T h := by
  rw [Expr.wk1, Expr.wk_eq_subst, stateMap, dispatch_subst S (fun v => literal_subst _ _)]
  rfl

private def mapResult (_B : Code) (h : S.Value → T.Value) : Expr Ops :=
  .case (.var 0) (.inl (.var 0)) (.inr (stateMap S T h))

private theorem mapResult_wf (h : S.Value → T.Value) :
    Wf (slot[Code.sum B S] :: Γ) (mapResult (Q := Q) (K := K) B h) (Code.sum B T).ty e :=
  .case (.var 0 bot_le) (.inl (.var 0 bot_le)) (.inr (map_wf h))

omit [HasEff (Opcode Q K) ε] [Preorder ε] [OrderBot ε] in
private theorem mapResult_subst (h : S.Value → T.Value) (σ : Nat → Expr Ops) :
    (mapResult B h).subst σ = .case (σ 0) (.inl (.var 0)) (.inr (stateMap S T h)) := by
  simp only [mapResult, Expr.subst, Expr.liftSubst, stateMap, dispatch_subst S (fun v => literal_subst _ _)]

omit [HasEff (Opcode Q K) ε] [Preorder ε] [OrderBot ε] in
private theorem mapResult_wk1 {h : S.Value → T.Value} :
    (mapResult (Q := Q) (K := K) B h).wk1 = mapResult B h := by
  rw [Expr.wk1, Expr.wk_eq_subst, mapResult_subst]
  rfl

private theorem mapResult_readback (h : S.Value → T.Value) (v : (Code.sum B S).Value) :
    Eqv Γ (Code.sum B T).ty e (.let₁ ((Code.sum B S).literal v) (mapResult B h) : Expr Ops)
      ((Code.sum B T).literal (Sum.map id h v)) := by
  have value : Wf Γ ((Code.sum B S).literal v : Expr Ops) (Code.sum B S).ty ⊥ := literal_wf _ _
  have beta := Eqv.step (.let1_beta value (mapResult_wf (Γ := Γ) (B := B) (e := e) h))
  rw [mapResult_subst] at beta
  have l : Wf (slot[B] :: Γ) (.inl (.var 0) : Expr Ops) (Code.sum B T).ty e := .inl (.var 0 bot_le)
  have r : Wf (slot[S] :: Γ) (.inr (stateMap S T h) : Expr Ops) (Code.sum B T).ty e := .inr (map_wf h)
  cases v with
  | inl v =>
      have p : Wf Γ (B.literal v : Expr Ops) B.ty ⊥ := literal_wf _ _
      exact beta.trans ((Eqv.step (.reduce (.case (.inl (p.weakenEffect bot_le)) l r)
        (.let₁ (p.weakenEffect bot_le) l) (.case_inl _ _ _))).trans (.step (.let1_beta p l)))
  | inr v =>
      have p : Wf Γ (S.literal v : Expr Ops) S.ty ⊥ := literal_wf _ _
      exact beta.trans ((Eqv.step (.reduce (.case (.inr (p.weakenEffect bot_le)) l r)
        (.let₁ (p.weakenEffect bot_le) r) (.case_inr _ _ _))).trans
        ((Eqv.step (.let1_beta p r)).trans (.inr (map_readback h v))))

private theorem case_row {L : Table Q K S B} {R : Table Q K T B}
    (h : S.Value → T.Value) (square : Commutes L R h) (s : S.Value)
    (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Eqv ([] : EffectCtx (Ty Unit) ε) (Code.sum B T).ty e
      (.case (L.row s) (.inl (.var 0)) (.inr (stateMap S T h))) (R.row (h s)) := by
  obtain ⟨head, replies⟩ := square s
  let request : Expr Ops := .op .ask (Q.literal (L.request s))
  have req : Wf ([] : EffectCtx (Ty Unit) ε) request K.ty e := .op hf (literal_wf _ _)
  have resL := replies_wf (Γ := []) (e := e) L s
  have wrap := mapResult_wf (Q := Q) (K := K) (Γ := []) (B := B) (e := e) h
  have wrap' := mapResult_wf (Q := Q) (K := K) (Γ := [slot[K]]) (B := B) (e := e) h
  have first : Eqv ([] : EffectCtx (Ty Unit) ε) (Code.sum B T).ty e
      (.case (L.row s) (.inl (.var 0)) (.inr (stateMap S T h))) (.let₁ (L.row s) (mapResult B h)) := by
    have lhs : Wf [slot[B]] (.inl (.var 0) : Expr Ops) (Code.sum B T).ty e := .inl (.var 0 bot_le)
    have rhs : Wf [slot[S]] (.inr (stateMap S T h) : Expr Ops) (Code.sum B T).ty e := .inr (map_wf h)
    have eq := case_eqv_bind (row_wf (Γ := []) L s hf) lhs rhs
    have ir : (.inr (stateMap S T h) : Expr Ops).wk1 = .inr (stateMap S T h) :=
      congrArg Expr.inr map_wk1
    rw [ir] at eq
    exact eq
  have assoc := Eqv.step (.rewrite (.let₁ (.let₁ req resL) wrap)
    (.let₁ req (.let₁ resL (mapResult_wk1.symm ▸ wrap'))) (.let1_let1 _ _ _))
  rw [mapResult_wk1] at assoc
  refine first.trans (assoc.trans ?_)
  unfold Table.row
  rw [← head]
  refine .let1 (.refl req) (eqv_by_codes K (.let₁ resL wrap') (replies_wf R (h s)) (fun v => ?_))
  simp only [Expr.subst, dispatch_subst K (fun v => literal_subst _ _), Expr.subst0,
    mapResult_subst, Expr.liftSubst]
  have left := dispatch_beta (Φ := Ops) (Γ := []) (e := e) K v
    (rows := fun r => (Code.sum B S).literal (L.reply s r))
    (fun v => literal_subst _ _) (fun _ => literal_wf _ _)
  have right := dispatch_beta (Φ := Ops) (Γ := []) (e := e) K v
    (rows := fun r => (Code.sum B T).literal (R.reply (h s) r))
    (fun v => literal_subst _ _) (fun _ => literal_wf _ _)
  have mapped := mapResult_readback (Q := Q) (K := K) (Γ := []) h (L.reply s v) (e := e)
  rw [replies v] at mapped
  exact (Eqv.let1 left (.refl wrap)).trans (mapped.trans right.symm)

theorem source_square {L : Table Q K S B} {R : Table Q K T B}
    (h : S.Value → T.Value) (square : Commutes L R h) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Eqv [slot[S]] (Code.sum B T).ty e
      (.case L.source (.inl (.var 0)) (.inr (stateMap S T h)))
      (T.dispatch R.row (stateMap S T h)) := by
  refine eqv_by_codes S (.case (step_wf L hf) (.inl (.var 0 bot_le)) (.inr (map_wf h)))
    (dispatch_wf T (fun t => row_wf R t hf) (map_wf h)) (fun s => ?_)
  simp only [Expr.subst, Table.source, dispatch_subst S (fun v => row_closed L v),
    dispatch_subst T (fun v => row_closed R v), stateMap,
    dispatch_subst S (fun v => literal_subst _ _), Expr.subst0, Expr.liftSubst]
  have read := dispatch_beta (Γ := []) S s (rows := L.row) (row_closed L) (fun v => row_wf L v hf)
  have arg := dispatch_beta (Φ := Ops) (Γ := []) (e := e) S s
    (rows := fun v => T.literal (h v)) (fun v => literal_subst _ _) (fun _ => literal_wf _ _)
  have right := dispatch_beta (Γ := []) T (h s) (rows := R.row) (row_closed R) (fun v => row_wf R v hf)
  exact (Eqv.case read (.refl (.inl (.var 0 bot_le))) (.refl (.inr (map_wf h)))).trans
    ((case_row h square s hf).trans (right.symm.trans (dispatch_eqv T (fun v => row_wf R v hf) arg.symm)))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Proofs
