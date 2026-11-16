module

public import Silmaril.Proofs.Wasm.Component.InstSem.Run

/-!
# Scripted components

When every core module denotes the strategy of a handler (a *script*: a fixed program for the
instantiation and for each export call), so does every component: `denIR_ofScripts` computes the
handler `compScriptH`, by the functor law `Strategy.ofHandler_comp`, the pairing law
`ofHandler_pair_ofHandler` and `ofHandler_id`. Bounding the core modules by scripts
(refinement, `denIR_mono`) bounds the component by the script of the component, whose program for
`inst` can be computed. The plays of a handler follow its programs (`handler_inst_plays`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- A script for each core module. -/
abbrev Scripts (M : Type) [CoreModule M] : Type :=
  (m : M) → Handler (CoreIface.sig (CoreModule.imports m))
    ((CoreIface.sig (CoreModule.exports m)).withInst Unit)

/-- The core semantics of scripts. -/
def CoreSemI.ofScripts (H : Scripts M) : CoreSemI M := ⟨fun m => Strategy.ofHandler (H m)⟩

/-- The script of `extI`. -/
def extScriptH (e : Nat) (D N : Handler sigU sigUI) : Handler sigU sigUI :=
  D.comp ((Handler.copair (Handler.id sigUI) ((exH sigU Unit).comp N)).comp (instSplitH e))

mutual
/-- The script of a component. -/
def compScriptH (H : Scripts M) : Comp M → Handler sigU sigUI
  | .mk I ns xs =>
    (nodesScriptH H I.length ns ((maskH I.length).comp (readyH sigU Unit))).comp
      (liftH (exportsH (envAfter I.length ns) xs))

/-- The script of nodes extending an environment. -/
def nodesScriptH (H : Scripts M) : Nat → List (Node M) → Handler sigU sigUI →
    Handler sigU sigUI
  | _, [], D => D
  | e, n :: ns, D => nodesScriptH H (e + n.width) ns (extScriptH e D (nodeScriptH H e n))

/-- The script of a node. -/
def nodeScriptH (H : Scripts M) : Nat → Node M → Handler sigU sigUI
  | e, .core m args =>
    (implsN e args (CoreModule.imports m).length).comp
      ((H m).comp (liftH (widenH (CoreModule.exports m).length)))
  | e, .inst c args => (implsH e args).comp (compScriptH H c)
end

open Strategy

theorem extI_ofHandler (e : Nat) (D N : Handler sigU sigUI) :
    extI e (ofHandler D) (ofHandler N) = ofHandler (extScriptH e D N) := by
  rw [extI, ← ofHandler_comp, ← ofHandler_id, ofHandler_pair_ofHandler, ← ofHandler_comp,
    ← ofHandler_comp, extScriptH]

mutual
/-- **A component of scripted modules is scripted.** -/
theorem denIR_ofScripts (H : Scripts M) :
    ∀ c : Comp M, c.denIR (CoreSemI.ofScripts H) = ofHandler (compScriptH H c)
  | .mk I ns xs => by
    rw [Comp.denIR, compScriptH, withReady, ← ofHandler_comp, nodesScriptH_eq H I.length ns,
      ← ofHandler_comp]

theorem nodesScriptH_eq (H : Scripts M) : ∀ (e : Nat) (ns : List (Node M))
    (D : Handler sigU sigUI),
    denNodesI (CoreSemI.ofScripts H) e ns (ofHandler D) = ofHandler (nodesScriptH H e ns D)
  | _, [], _ => by simp only [denNodesI, nodesScriptH]
  | e, n :: ns, D => by
    rw [denNodesI, nodesScriptH, nodeScriptH_den H e n, extI_ofHandler, nodesScriptH_eq H _ ns]

theorem nodeScriptH_den (H : Scripts M) : ∀ (e : Nat) (n : Node M),
    n.denI (CoreSemI.ofScripts H) e = ofHandler (nodeScriptH H e n)
  | e, .core m args => by
    rw [Node.denI, nodeScriptH, coreNodeI, ofHandler_comp, ofHandler_comp]
    rfl
  | e, .inst c args => by
    rw [Node.denI, nodeScriptH, denIR_ofScripts H c, ofHandler_comp]
end

/-! ## Plays of scripts -/

/-- The calls a program may make, in order, are among `L` (a prefix of `L` is made, whatever
the answers). -/
inductive Prog.AsksWithin {E : Sig.{0}} {A : Type} : Prog E A → List E.Op → Prop
  | pure (a : A) (L : List E.Op) : Prog.AsksWithin (.pure a) L
  | call {m : E.Op} {k : E.Ar m → Prog E A} {L : List E.Op} :
      (∀ n, Prog.AsksWithin (k n) L) → Prog.AsksWithin (.call m k) (m :: L)

/-- The lower questions of a play. -/
def lowerAsks {E F : Sig.{0}} : List (Move E F) → List E.Op
  | [] => []
  | .inl (.ask m) :: p => m :: lowerAsks p
  | _ :: p => lowerAsks p

theorem lowerAsks_append {E F : Sig.{0}} : ∀ (p q : List (Move E F)),
    lowerAsks (p ++ q) = lowerAsks p ++ lowerAsks q
  | [], _ => rfl
  | .inl (.ask m) :: p, q => by simp only [List.cons_append, lowerAsks, lowerAsks_append p q]
  | .inl (.ans _ _) :: p, q => by simp only [List.cons_append, lowerAsks, lowerAsks_append p q]
  | .inr _ :: p, q => by simp only [List.cons_append, lowerAsks, lowerAsks_append p q]

section Handler

variable {E F : Sig.{0}} {h : Handler E F}

/-- From a program whose calls are among `L`, a run of the handler asks a prefix of `L` before
answering, after which it is idle. -/
theorem handler_run_asks {q : F.Op} : ∀ {P : Prog E (F.Ar q)} {L : List E.Op}
    {x : h.toReduction.toLTS.State} {p : List (Move E F)},
    Prog.AsksWithin P L → h.toReduction.toLTS.Run (.run q P) p x →
      (lowerAsks p <+: L ∧ (∀ a, Sum.inr (Ev.ans q a) ∉ p)) ∨
      ∃ a p₁ p₂, p = p₁ ++ .inr (.ans q a) :: p₂ ∧ lowerAsks p₁ <+: L ∧
        (∀ a', Sum.inr (Ev.ans q a') ∉ p₁) ∧ h.toReduction.toLTS.Run .idle p₂ x := by
  intro P L x p hP hr
  induction hP generalizing x p with
  | pure a L =>
    rcases p with _ | ⟨o, p⟩
    · exact .inl ⟨List.nil_prefix, fun _ h => by simp at h⟩
    · obtain ⟨y, hs, hr'⟩ := handler_run_cons hr
      cases hs with
      | call hc => cases hc
      | ret hd =>
        cases hd
        exact .inr ⟨a, [], p, rfl, List.nil_prefix, fun _ h => by simp at h, hr'⟩
  | @call m k L hk ih =>
    rcases p with _ | ⟨o, p⟩
    · exact .inl ⟨List.nil_prefix, fun _ h => by simp at h⟩
    · obtain ⟨y, hs, hr'⟩ := handler_run_cons hr
      cases hs with
      | ret hd => cases hd
      | call hc =>
        cases hc
        rcases p with _ | ⟨o', p⟩
        · exact .inl ⟨by simp [lowerAsks], by simp⟩
        · obtain ⟨y', hs', hr''⟩ := handler_run_cons hr'
          cases hs' with
          | resume _ _ _ n =>
            rcases ih n hr'' with ⟨h1, h2⟩ | ⟨a, p₁, p₂, rfl, h1, h2, h3⟩
            · refine .inl ⟨?_, ?_⟩
              · simpa [lowerAsks] using h1
              · intro a ha
                simp only [List.mem_cons, reduceCtorEq, false_or] at ha
                exact h2 a ha
            · refine .inr ⟨a, .inl (.ask m) :: .inl (.ans m n) :: p₁, p₂, rfl, ?_, ?_, h3⟩
              · simpa [lowerAsks] using h1
              · intro a' ha
                simp only [List.mem_cons, reduceCtorEq, false_or] at ha
                exact h2 a' ha

end Handler

end Silmaril.Proofs.Wasm.Component.InstSem
