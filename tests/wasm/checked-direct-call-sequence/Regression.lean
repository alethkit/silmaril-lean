module

import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame Value)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Numerics (Profile intBinOp)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence

open OuterCall.Computed

private abbrev i32 := Value.int .i32
private abbrev int32 := NumType.int .i32

private def firstCallee : CallFrame.Callee := ⟨{}, ⟨0⟩, [int32], [], some int32, .ret [i32 7]⟩
private def trappingCallee : CallFrame.Callee := { firstCallee with program := .unreachable }
private def secondCallee : CallFrame.Callee := ⟨{}, ⟨0⟩, [int32], [], some int32, .locals [.get ⟨0⟩]⟩
private def caller : Frame := ⟨[i32 5, i32 2, i32 3, i32 0], { funcs := [⟨0⟩, ⟨1⟩] }⟩
private def saved : List Value := [i32 3]

private def site (fn : CallFrame.Callee) : Site :=
  ⟨caller, [⟨⟨0⟩, ⟨0⟩, fn⟩, ⟨⟨1⟩, ⟨1⟩, secondCallee⟩], [int32]⟩

private def firstId (fn : CallFrame.Callee) : (site fn).TargetId :=
  ⟨0, by change 0 < 2; decide⟩

private def secondId (fn : CallFrame.Callee) : (site fn).TargetId :=
  ⟨1, by change 1 < 2; decide⟩

private def continuation (fn : CallFrame.Callee) : List (Op (site fn)) :=
  [.numeric (.get ⟨1⟩), .numeric (.bin .i32 .mul), .numeric (.bin .i32 .add)]

private def later (fn : CallFrame.Callee) : List (Op (site fn)) := .call (secondId fn) :: continuation fn

private def code (fn : CallFrame.Callee) : List (Op (site fn)) :=
  [.numeric (.get ⟨0⟩), .call (firstId fn)] ++ later fn

private def store (fn : CallFrame.Callee) : V1.Execution.Store Unit :=
  { funcs := [.wasm fn.type fn.module fn.v1Func, .wasm secondCallee.type secondCallee.module secondCallee.v1Func] }

private theorem registered (fn : CallFrame.Callee) (typed : fn.program.Typed fn)
    (readOnly : OuterCall.Computed.Sequence.Composed.ReadOnly fn.program) : V1Guard (store fn) (site fn) := by
  have casesId (id : (site fn).TargetId) : id = firstId fn ∨ id = secondId fn := by
    have bound : id.val < 2 := id.isLt
    have casesVal : id.val = 0 ∨ id.val = 1 := by omega
    exact casesVal.elim (fun h => .inl (Fin.ext h)) (fun h => .inr (Fin.ext h))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro id
    rcases casesId id with rfl | rfl
    · exact readOnly
    · simp [Site.target, site, secondId, secondCallee, OuterCall.Computed.Sequence.Composed.ReadOnly]
  · intro id
    rcases casesId id with rfl | rfl
    · exact typed
    · rfl
  · intro id
    rcases casesId id with rfl | rfl <;> rfl
  · intro id
    rcases casesId id with rfl | rfl <;> rfl

private theorem firstInvokes (fn : CallFrame.Callee) (count : fn.params.length = 1) :
    Runs (site fn) (.running saved (code fn)) (.active (firstId fn) (.invoke saved [i32 5]) (later fn)) := by
  have load : Edge (site fn) (.running saved (code fn))
      (.running (saved ++ [i32 5]) (.call (firstId fn) :: later fn)) :=
    fact (.numeric (.get rfl))
  exact (Relation.ReflTransGen.single load).tail
    (fact (.resolve (firstId fn) saved [i32 5] (later fn) count.symm))

private def entered (fn : CallFrame.Callee) : State (site fn) :=
  .active (firstId fn) (.label saved [i32 5] (.code fn.program)) (later fn)

private theorem firstEnters (fn : CallFrame.Callee) (count : fn.params.length = 1) (locals : fn.locals = []) :
    Runs (site fn) (.running saved (code fn)) (entered fn) := by
  have enter := (firstInvokes fn count).tail (call (by trivial) (CallFrame.fact (.enter saved [i32 5] count.symm)))
  simpa [entered, attach, Site.target, site, firstId, CallFrame.Callee.init, locals] using enter

private theorem firstReturns :
    Runs (site firstCallee) (entered firstCallee)
      (.running (saved ++ [i32 7]) (later firstCallee)) := by
  have pop := Relation.ReflTransGen.single
    (call (i := firstId firstCallee) (rest := later firstCallee) (by trivial)
      (CallFrame.fact (.labelReturn saved [i32 5] [i32 7])))
  exact pop.tail (call (by trivial) (CallFrame.fact (.frameReturn saved [i32 5] [] [i32 7] rfl)))

private theorem resolveSecond : Edge (site firstCallee) (.running (saved ++ [i32 7]) (later firstCallee))
    (.active (secondId firstCallee) (.invoke saved [i32 7]) (continuation firstCallee)) :=
  fact (.resolve (secondId firstCallee) saved [i32 7] (continuation firstCallee) rfl)

private theorem secondInvokes :
    Runs (site firstCallee) (.running saved (code firstCallee))
      (.active (secondId firstCallee) (.invoke saved [i32 7]) (continuation firstCallee)) :=
  ((firstEnters firstCallee rfl rfl).trans firstReturns).tail resolveSecond

private theorem secondReturns {s : Site} (i : s.TargetId) (declared : (s.target i).callee = secondCallee)
    (below : List Value) (arg : Value) (rest : List (Op s)) :
    Runs s (.active i (.invoke below [arg]) rest) (.running (below ++ [arg]) rest) := by
  have enter : CallFrame.Edge (s.target i).callee (.invoke below [arg])
      (.label below [arg] (.code secondCallee.program)) := by
    rw [declared]
    exact CallFrame.fact (.enter below [arg] rfl)
  have read := (Relation.ReflTransGen.single (call (i := i) (rest := rest) (by trivial) enter)).tail
    (call (by trivial) (CallFrame.reduce below (Locals.fact (.get [arg] ⟨0⟩ arg rfl))))
  have label := read.tail (call (by trivial) (CallFrame.fact (.labelValues below [arg] [arg])))
  have pop : CallFrame.Edge (s.target i).callee (.exit below [arg] (.values [arg])) (.returned below [arg]) := by
    rw [declared]
    exact CallFrame.fact (.frameValues below [arg] [arg] rfl)
  exact label.tail (call (by trivial) pop)

private theorem normalAfterEntry : Runs (site firstCallee) (entered firstCallee) (.running [i32 17] []) := by
  have returned := (firstReturns.tail resolveSecond).trans (secondReturns (secondId firstCallee) rfl saved (i32 7) (continuation firstCallee))
  have load := returned.tail (fact (.numeric (.get rfl)))
  have mul : intBinOp .i32 .mul 7 2 = .ok 14 := rfl
  have product := load.tail (fact (.numeric (.bin (stack := saved) mul)))
  have add : intBinOp .i32 .add 3 14 = .ok 17 := rfl
  exact product.tail (fact (.numeric (.bin (stack := []) add)))

private theorem normalPath : Runs (site firstCallee) (.running saved (code firstCallee)) (.running [i32 17] []) :=
  (firstEnters firstCallee rfl rfl).trans normalAfterEntry

private theorem firstRaises :
    Runs (site trappingCallee) (entered trappingCallee) (.trapped saved (later trappingCallee)) := by
  have raises := Relation.ReflTransGen.single
    (call (i := firstId trappingCallee) (rest := later trappingCallee) (by trivial)
      (CallFrame.fact (.unreachable saved [i32 5])))
  have label := raises.tail (call (by trivial) (CallFrame.fact (.labelTrap saved [i32 5])))
  exact label.tail (call (by trivial) (CallFrame.fact (.frameTrap saved [i32 5])))

private theorem dropSecond : Edge (site trappingCallee) (.trapped saved (later trappingCallee))
    (.trapped saved (continuation trappingCallee)) :=
  fact (.discard (.cut saved [] [Op.call (secondId trappingCallee)] (continuation trappingCallee) (.inr (by simp))))

private theorem trapAfterEntry : Runs (site trappingCallee) (entered trappingCallee) (.trapped [] []) :=
  (firstRaises.tail dropSecond).tail
    (fact (.discard (.cut [] saved (continuation trappingCallee) [] (.inl (by simp [saved])))))

private theorem trapPath : Runs (site trappingCallee) (.running saved (code trappingCallee)) (.trapped [] []) :=
  (firstEnters trappingCallee rfl rfl).trans trapAfterEntry

example : V1.Execution.Steps CallFrame.v1NoHost (v1Config (store firstCallee) (site firstCallee)
    (.running saved (code firstCallee))) ⟨store firstCallee, caller, [.source (.intConst .i32 17)]⟩ :=
  (v1_run_iff (registered firstCallee rfl trivial) (a := .running saved (code firstCallee)) rfl).mpr
    ⟨_, normalPath, rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (v1Config (store firstCallee) (site firstCallee) (.running saved (code firstCallee))).toLime
    ⟨(store firstCallee).mapCode V1.Func.toLime, caller, [.source (.intConst .i32 3), .source (.intConst .i32 7),
      .invoke ⟨1⟩, .source (.localGet ⟨1⟩), .source (.intBinOp .i32 .mul), .source (.intBinOp .i32 .add)]⟩ := by
  rw [v1_to_lime]
  have g := guard_to_lime (registered firstCallee rfl trivial)
  exact (lime_run_iff g (a := .running saved (code firstCallee)) rfl).mpr
    ⟨_, secondInvokes, ⟨trivial, ⟨rfl, rfl⟩, rfl⟩, rfl⟩

example : Core.Steps Profile.spec noHost
    (v1Config (store trappingCallee) (site trappingCallee) (.running saved (code trappingCallee))).toLime.toCore
    ⟨((store trappingCallee).mapCode V1.Func.toLime).toCore, caller.toCore, [.trap]⟩ := by
  have g := guard_to_lime (registered trappingCallee trivial trivial)
  rw [v1_to_lime, lime_to_core g]
  exact (core_run_iff (guard_to_core g) (a := .running saved (code trappingCallee)) rfl).mpr
    ⟨_, trapPath, trivial, rfl⟩

example : Core.Step Profile.spec noHost
    (v1Config (store trappingCallee) (site trappingCallee) (.trapped saved (later trappingCallee))).toLime.toCore
    ⟨((store trappingCallee).mapCode V1.Func.toLime).toCore, caller.toCore,
      [.plain (.intConst .i32 3), .trap, .plain (.localGet ⟨1⟩), .plain (.intBinOp .i32 .mul),
        .plain (.intBinOp .i32 .add)]⟩ := by
  have g := guard_to_lime (registered trappingCallee trivial trivial)
  rw [v1_to_lime, lime_to_core g]
  exact core_sound (guard_to_core g) dropSecond

example {target : Core.Config Unit}
    (path : Core.Steps Profile.spec noHost
      (v1Config (store trappingCallee) (site trappingCallee) (.trapped saved (later trappingCallee))).toLime.toCore target) :
    ∃ kept rest, target =
      (v1Config (store trappingCallee) (site trappingCallee) (.trapped kept rest)).toLime.toCore := by
  have g := guard_to_lime (registered trappingCallee trivial trivial)
  rw [v1_to_lime, lime_to_core g] at path
  obtain ⟨phase, run, _, eq⟩ := (core_run_iff (guard_to_core g) (a := .trapped saved (later trappingCallee)) trivial).mp path
  obtain ⟨kept, rest, rfl⟩ := trap_bypasses run
  exact ⟨kept, rest, by rw [v1_to_lime, lime_to_core g, eq]⟩

example : ¬ Admitted (site firstCallee) (.running [] [.call (firstId firstCallee)]) := by
  intro ready
  change (none : Option (List NumType)) = some [int32] at ready
  cases ready

open OuterCall

private def parent : Frame := ⟨[i32 99, i32 0], { funcs := [⟨2⟩] }⟩

private def outerSite (fn : CallFrame.Callee) : DirectSequence.Site :=
  ⟨⟨0⟩, ⟨2⟩, [i32 5, i32 2, i32 3], caller.module, ⟨0⟩,
    [int32, int32, int32], [int32], some int32, (site fn).targets⟩

private def outer (fn : CallFrame.Callee) : DirectSequence.Program :=
  ⟨outerSite fn, .numeric (.get ⟨2⟩) :: code fn⟩

private def outerStore (fn : CallFrame.Callee) : V1.Execution.Store Unit :=
  { store fn with funcs := (store fn).funcs ++
    [.wasm (outerSite fn).type (outerSite fn).module (outer fn).v1Func] }

private theorem outerGuard (fn : CallFrame.Callee) (g : V1Guard (store fn) (site fn)) (typed : DirectSequence.Typed (outer fn)) :
    DirectSequence.V1Guard (outerStore fn) parent (outer fn) := by
  refine ⟨⟨typed, rfl⟩, rfl, ⟨g.readOnly, g.typed, g.resolves, ?_⟩⟩
  intro i
  have allocated := g.allocated i
  have bound : ((site fn).target i).address.value < (store fn).funcs.length :=
    List.getElem?_eq_some_iff.mp allocated |>.1
  change ((store fn).funcs ++ _)[((site fn).target i).address.value]? = _
  rwa [List.getElem?_append_left bound]

private theorem regularGuard : DirectSequence.V1Guard (outerStore firstCallee) parent (outer firstCallee) :=
  outerGuard firstCallee (registered firstCallee rfl trivial) ⟨rfl, rfl, by decide⟩

private theorem failingGuard : DirectSequence.V1Guard (outerStore trappingCallee) parent (outer trappingCallee) :=
  outerGuard trappingCallee (registered trappingCallee trivial trivial) ⟨rfl, rfl, by decide⟩

private theorem fromCall (fn : CallFrame.Callee) {target : State (site fn)}
    (bodyRun : Runs (site fn) (.running saved (code fn)) target) :
    DirectSequence.Runs (outer fn) .call (.label target) := by
  have resolve : DirectSequence.Edge (outer fn) .call .invoke := DirectSequence.fact .resolve
  have enter := (Relation.ReflTransGen.single resolve).tail (DirectSequence.fact .enter)
  have load : Edge (site fn) (.running [] ((outer fn).code)) (.running saved (code fn)) :=
    fact (.numeric (.get rfl))
  exact enter.trans (DirectSequence.label_run ((Relation.ReflTransGen.single load).trans bodyRun))

private theorem outerFinishes (fn : CallFrame.Callee) {a b : State (outer fn).site.body}
    {r : Nested.Result} (body : Runs (outer fn).site.body a b) (finished : DirectSequence.Finished _ b r)
    (arity : DirectSequence.ResultArity (outer fn).site r) :
    DirectSequence.Runs (outer fn) (.label a) (.done r) :=
  ((DirectSequence.label_run body).tail (DirectSequence.fact (.leaveLabel finished))).tail
    (DirectSequence.fact (.leaveFrame r arity))

private theorem outerNormal : DirectSequence.Runs (outer firstCallee) .call (.done (.values [i32 17])) :=
  ((fromCall firstCallee normalPath).tail (DirectSequence.fact (.leaveLabel (.values _)))).tail
    (DirectSequence.fact (.leaveFrame (.values [i32 17]) rfl))

private theorem outerTrap : DirectSequence.Runs (outer trappingCallee) .call (.done .trap) :=
  ((fromCall trappingCallee trapPath).tail (DirectSequence.fact (.leaveLabel .trap))).tail
    (DirectSequence.fact (.leaveFrame .trap trivial))

example : V1.Execution.Steps CallFrame.v1NoHost
    ⟨outerStore firstCallee, parent, V1.Execution.values (outerSite firstCallee).args ++ [.source (.call ⟨0⟩)]⟩
    ⟨outerStore firstCallee, parent, [.source (.intConst .i32 17)]⟩ :=
  (DirectSequence.v1_run_iff regularGuard (a := .call) trivial).mpr ⟨_, outerNormal, rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (DirectSequence.v1Config (outerStore firstCallee) parent (outer firstCallee).site .call).toLime
    ⟨(outerStore firstCallee).mapCode V1.Func.toLime, parent, [.source (.intConst .i32 17)]⟩ := by
  rw [DirectSequence.v1_to_lime]
  exact (DirectSequence.lime_run_iff (DirectSequence.guard_to_lime regularGuard) (a := .call) trivial).mpr
    ⟨_, outerNormal, rfl, rfl⟩

example : Core.Steps Profile.spec noHost
    (DirectSequence.v1Config (outerStore trappingCallee) parent (outer trappingCallee).site .call).toLime.toCore
    ⟨((outerStore trappingCallee).mapCode V1.Func.toLime).toCore, parent.toCore, [.trap]⟩ := by
  have g := DirectSequence.guard_to_lime failingGuard
  rw [DirectSequence.v1_to_lime, DirectSequence.lime_to_core g]
  exact (DirectSequence.core_run_iff (DirectSequence.guard_to_core g) (a := .call) trivial).mpr
    ⟨_, outerTrap, trivial, rfl⟩

example {target : Core.Config Unit}
    (path : Core.Steps Profile.spec noHost
      (DirectSequence.v1Config (outerStore trappingCallee) parent (outer trappingCallee).site
        (.label (.trapped saved (later trappingCallee)))).toLime.toCore target) :
    ∃ phase, DirectSequence.Unwinding (outer trappingCallee).site phase ∧
      target = (DirectSequence.v1Config (outerStore trappingCallee) parent (outer trappingCallee).site phase).toLime.toCore := by
  have g := DirectSequence.guard_to_lime failingGuard
  rw [DirectSequence.v1_to_lime, DirectSequence.lime_to_core g] at path
  obtain ⟨phase, run, _, read⟩ := (DirectSequence.core_run_iff (p := outer trappingCallee) (DirectSequence.guard_to_core g)
    (a := .label (.trapped saved (later trappingCallee))) trivial).mp path
  exact ⟨phase, DirectSequence.trap_bypasses (.label _ _) run,
    by rw [DirectSequence.v1_to_lime, DirectSequence.lime_to_core g, read]⟩

open DirectSequence

private def afterAdd : List Prefix.Op := [.get ⟨0⟩, .bin .i32 .add]

private def enclosing : Enclosing.Context := Enclosing.Context.numeric parent [i32 11] (.bin .i32 .add :: afterAdd) [int32]

private def afterAddCode : List (Op enclosing.sequence) := afterAdd.map .numeric

private theorem enclosingGuard (fn : CallFrame.Callee) (g : DirectSequence.V1Guard (outerStore fn) parent (outer fn)) :
    Enclosing.V1Guard (outerStore fn) enclosing (outer fn) := by
  refine ⟨g, ⟨?_, ?_, ?_, ?_⟩⟩ <;> intro i <;> exact Fin.elim0 i

private theorem enclosingTyped (fn : CallFrame.Callee) : enclosing.Typed (outer fn) := rfl

private theorem restored :
    Enclosing.Runs enclosing (outer firstCallee) (.active .call)
      (.resume [i32 11, i32 17] enclosing.continuation) :=
  Enclosing.invoke_run (ctx := enclosing) outerNormal

private theorem continued :
    Enclosing.Runs enclosing (outer firstCallee) (.active .call) (.resume [i32 127] []) := by
  have firstAdd : intBinOp .i32 .add 11 17 = .ok 28 := rfl
  have sum := restored.tail (Enclosing.resume (fact (.numeric (.bin (stack := []) firstAdd))))
  have load : Enclosing.Edge enclosing (outer firstCallee) (.resume [i32 28] afterAddCode)
      (.resume [i32 28, i32 99] [.numeric (.bin .i32 .add)]) := Enclosing.resume (fact (.numeric (.get rfl)))
  have lastAdd : intBinOp .i32 .add 28 99 = .ok 127 := rfl
  exact (sum.tail load).tail (Enclosing.resume (fact (.numeric (.bin (stack := []) lastAdd))))

private theorem outerBubbled :
    Enclosing.Runs enclosing (outer trappingCallee) (.active .call) (.trapped enclosing.saved enclosing.continuation) :=
  Enclosing.invoke_run (ctx := enclosing) outerTrap

private theorem discardOne :
    Enclosing.Edge enclosing (outer trappingCallee) (.trapped enclosing.saved enclosing.continuation)
      (.trapped enclosing.saved afterAddCode) := by
  apply Enclosing.resume (fact (.discard ?_))
  have code : [.numeric (.bin .i32 .add)] ++ afterAddCode = enclosing.continuation := rfl
  rw [← code]
  simpa only [List.append_nil] using
    Prefix.Discard.cut enclosing.saved [] ([.numeric (.bin .i32 .add)] : List (Op enclosing.sequence)) afterAddCode
      (.inr (by simp))

private theorem bubbled :
    Enclosing.Runs enclosing (outer trappingCallee) (.active .call) (.trapped [] []) := by
  have dropStack : Enclosing.Edge enclosing (outer trappingCallee) (.trapped enclosing.saved afterAddCode)
      (.trapped [] afterAddCode) :=
    Enclosing.resume (fact (.discard (.cut [] enclosing.saved [] afterAddCode (.inl (by decide)))))
  have dropRest : Enclosing.Edge enclosing (outer trappingCallee) (.trapped [] afterAddCode) (.trapped [] []) :=
    Enclosing.resume (fact (.discard (.cut [] [] afterAddCode [] (.inr (by decide)))))
  exact ((outerBubbled.tail discardOne).tail dropStack).tail dropRest

example : V1.Execution.Steps CallFrame.v1NoHost
    (Enclosing.v1Config (outerStore firstCallee) enclosing (outer firstCallee).site (.active .call))
    ⟨outerStore firstCallee, parent, [.source (.intConst .i32 11), .source (.intConst .i32 17),
      .source (.intBinOp .i32 .add), .source (.localGet ⟨0⟩), .source (.intBinOp .i32 .add)]⟩ :=
  (Enclosing.v1_run_iff (enclosingGuard firstCallee regularGuard) (enclosingTyped firstCallee) (a := .active .call) ⟨trivial, trivial⟩).mpr
    ⟨_, restored, rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (Enclosing.v1Config (outerStore firstCallee) enclosing (outer firstCallee).site (.active .call)).toLime
    ⟨(outerStore firstCallee).mapCode V1.Func.toLime, parent, [.source (.intConst .i32 127)]⟩ := by
  rw [Enclosing.v1_to_lime]
  exact (Enclosing.lime_run_iff (Enclosing.guard_to_lime (enclosingGuard firstCallee regularGuard)) (enclosingTyped firstCallee)
    (a := .active .call) ⟨trivial, trivial⟩).mpr ⟨_, continued, rfl, rfl⟩

example : Lime1.Execution.Step CallFrame.limeNoHost
    (Enclosing.v1Config (outerStore trappingCallee) enclosing (outer trappingCallee).site
      (.trapped enclosing.saved enclosing.continuation)).toLime
    ⟨(outerStore trappingCallee).mapCode V1.Func.toLime, parent, [.source (.intConst .i32 11),
      .trap, .source (.localGet ⟨0⟩), .source (.intBinOp .i32 .add)]⟩ := by
  rw [Enclosing.v1_to_lime]
  exact Enclosing.lime_sound (Enclosing.guard_to_lime (enclosingGuard trappingCallee failingGuard)) discardOne

example : Core.Steps Profile.spec noHost
    (Enclosing.v1Config (outerStore trappingCallee) enclosing (outer trappingCallee).site (.active .call)).toLime.toCore
    ⟨((outerStore trappingCallee).mapCode V1.Func.toLime).toCore, parent.toCore, [.trap]⟩ := by
  have g := Enclosing.guard_to_lime (enclosingGuard trappingCallee failingGuard)
  rw [Enclosing.v1_to_lime, Enclosing.lime_to_core g]
  exact (Enclosing.core_run_iff (Enclosing.guard_to_core g) (enclosingTyped trappingCallee)
    (a := .active .call) ⟨trivial, trivial⟩).mpr ⟨_, bubbled, trivial, rfl⟩

private def firstOuterTrap : Enclosing.State enclosing (outer trappingCallee).site :=
  .active (.label (.trapped saved (later trappingCallee)))

example {target : Core.Config Unit}
    (path : Core.Steps Profile.spec noHost
      (Enclosing.v1Config (outerStore trappingCallee) enclosing (outer trappingCallee).site firstOuterTrap).toLime.toCore target) :
    ∃ phase, Enclosing.Unwinding enclosing (outer trappingCallee).site phase ∧
      target = (Enclosing.v1Config (outerStore trappingCallee) enclosing
        (outer trappingCallee).site phase).toLime.toCore := by
  have g := Enclosing.guard_to_lime (enclosingGuard trappingCallee failingGuard)
  rw [Enclosing.v1_to_lime, Enclosing.lime_to_core g] at path
  obtain ⟨phase, run, _, eq⟩ := (Enclosing.core_run_iff (Enclosing.guard_to_core g) (enclosingTyped trappingCallee)
    (a := firstOuterTrap) ⟨trivial, trivial⟩).mp path
  exact ⟨phase, Enclosing.trap_bypasses (.active (.label _ _) trivial) run,
    by rw [Enclosing.v1_to_lime, Enclosing.lime_to_core g, eq]⟩

private def callParent : Frame :=
  { parent with module := { parent.module with funcs := [⟨2⟩, ⟨1⟩] } }

private def callSequence : Site := ⟨callParent, [⟨⟨1⟩, ⟨1⟩, secondCallee⟩], [int32]⟩
private def continuationTarget : callSequence.TargetId := ⟨0, by decide⟩
private def afterCall : List (Op callSequence) := [.numeric (.bin .i32 .add)]
private def enclosingCall : Enclosing.Context :=
  ⟨callSequence, [i32 11], .call continuationTarget :: afterCall⟩

private theorem enclosingCallTyped (fn : CallFrame.Callee) : enclosingCall.Typed (outer fn) := rfl

private theorem enclosingCallGuard (fn : CallFrame.Callee)
    (g : DirectSequence.V1Guard (outerStore fn) parent (outer fn)) :
    Enclosing.V1Guard (outerStore fn) enclosingCall (outer fn) := by
  have onlyTarget (i : callSequence.TargetId) : i = continuationTarget := by
    have bound : i.val < 1 := i.isLt
    exact Fin.ext (by change i.val = 0; omega)
  refine ⟨⟨⟨g.typed, rfl⟩, g.allocated, g.body⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro i
    rw [onlyTarget i]
    simp [enclosingCall, Site.target, callSequence, continuationTarget, secondCallee,
      OuterCall.Computed.Sequence.Composed.ReadOnly]
  · intro i
    rw [onlyTarget i]
    rfl
  · intro i
    rw [onlyTarget i]
    rfl
  · intro i
    rw [onlyTarget i]
    rfl

private theorem callRestored :
    Enclosing.Runs enclosingCall (outer firstCallee) (.active .call)
      (.resume [i32 11, i32 17] enclosingCall.continuation) :=
  Enclosing.invoke_run (ctx := enclosingCall) outerNormal

private theorem callResolved :
    Enclosing.Runs enclosingCall (outer firstCallee) (.active .call)
      (.continuation (.active continuationTarget (.invoke [i32 11] [i32 17]) afterCall)) :=
  callRestored.tail (Enclosing.resume (fact (.resolve continuationTarget [i32 11] [i32 17] afterCall rfl)))

private theorem resumeAfterResolve {a : Enclosing.State enclosingCall (outer firstCallee).site}
    (resolved : Enclosing.Runs enclosingCall (outer firstCallee) a
      (.continuation (.active continuationTarget (.invoke [i32 11] [i32 17]) afterCall))) :
    Enclosing.Runs enclosingCall (outer firstCallee) a (.resume [i32 28] []) := by
  have returned := resolved.trans (Enclosing.resume_run
    (secondReturns continuationTarget rfl [i32 11] (i32 17) afterCall))
  have add : intBinOp .i32 .add 11 17 = .ok 28 := rfl
  exact returned.tail (Enclosing.resume (fact (.numeric (.bin (stack := []) add))))

private theorem callContinued :
    Enclosing.Runs enclosingCall (outer firstCallee) (.active .call) (.resume [i32 28] []) :=
  resumeAfterResolve callResolved

private theorem discardContinuationCall :
    Enclosing.Edge enclosingCall (outer trappingCallee) (.trapped enclosingCall.saved enclosingCall.continuation)
      (.trapped enclosingCall.saved afterCall) := by
  apply Enclosing.resume (fact (.discard ?_))
  simpa only [List.append_nil, List.cons_append, List.nil_append, enclosingCall] using
    Prefix.Discard.cut enclosingCall.saved [] ([.call continuationTarget] : List (Op callSequence)) afterCall
      (.inr (by simp))

private theorem unwindAfterTrap {a : Enclosing.State enclosingCall (outer trappingCallee).site}
    (unwind : Enclosing.Runs enclosingCall (outer trappingCallee) a
      (.trapped enclosingCall.saved enclosingCall.continuation)) :
    Enclosing.Runs enclosingCall (outer trappingCallee) a (.trapped [] []) :=
  (unwind.tail discardContinuationCall).tail (Enclosing.resume (fact (.discard
    (.cut [] enclosingCall.saved afterCall [] (.inl (by decide))))))

private theorem callTrap :
    Enclosing.Runs enclosingCall (outer trappingCallee) (.active .call) (.trapped [] []) :=
  unwindAfterTrap (Enclosing.invoke_run outerTrap)

example : V1.Execution.Steps CallFrame.v1NoHost
    (Enclosing.v1Config (outerStore firstCallee) enclosingCall (outer firstCallee).site (.active .call))
    ⟨outerStore firstCallee, callParent, [.source (.intConst .i32 11), .source (.intConst .i32 17),
      .source (.call ⟨1⟩), .source (.intBinOp .i32 .add)]⟩ :=
  (Enclosing.v1_run_iff (enclosingCallGuard firstCallee regularGuard) (enclosingCallTyped firstCallee)
    (a := .active .call) ⟨trivial, trivial⟩).mpr ⟨_, callRestored, rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (Enclosing.v1Config (outerStore firstCallee) enclosingCall (outer firstCallee).site (.active .call)).toLime
    ⟨(outerStore firstCallee).mapCode V1.Func.toLime, callParent, [.source (.intConst .i32 11), .source (.intConst .i32 17),
      .invoke ⟨1⟩, .source (.intBinOp .i32 .add)]⟩ := by
  rw [Enclosing.v1_to_lime]
  have g := Enclosing.guard_to_lime (enclosingCallGuard firstCallee regularGuard)
  exact (Enclosing.lime_run_iff g (enclosingCallTyped firstCallee) (a := .active .call) ⟨trivial, trivial⟩).mpr
    ⟨_, callResolved, ⟨trivial, ⟨rfl, rfl⟩, rfl⟩, rfl⟩

example : Core.Steps Profile.spec noHost
    (Enclosing.v1Config (outerStore firstCallee) enclosingCall (outer firstCallee).site (.active .call)).toLime.toCore
    ⟨((outerStore firstCallee).mapCode V1.Func.toLime).toCore, callParent.toCore, [.plain (.intConst .i32 28)]⟩ := by
  have g := Enclosing.guard_to_lime (enclosingCallGuard firstCallee regularGuard)
  rw [Enclosing.v1_to_lime, Enclosing.lime_to_core g]
  exact (Enclosing.core_run_iff (Enclosing.guard_to_core g) (enclosingCallTyped firstCallee)
    (a := .active .call) ⟨trivial, trivial⟩).mpr ⟨_, callContinued, rfl, rfl⟩

example : Core.Steps Profile.spec noHost
    (Enclosing.v1Config (outerStore trappingCallee) enclosingCall (outer trappingCallee).site (.active .call)).toLime.toCore
    ⟨((outerStore trappingCallee).mapCode V1.Func.toLime).toCore, callParent.toCore, [.trap]⟩ := by
  have g := Enclosing.guard_to_lime (enclosingCallGuard trappingCallee failingGuard)
  rw [Enclosing.v1_to_lime, Enclosing.lime_to_core g]
  exact (Enclosing.core_run_iff (Enclosing.guard_to_core g) (enclosingCallTyped trappingCallee)
    (a := .active .call) ⟨trivial, trivial⟩).mpr ⟨_, callTrap, trivial, rfl⟩

example : Lime1.Execution.Step CallFrame.limeNoHost
    (Enclosing.v1Config (outerStore trappingCallee) enclosingCall (outer trappingCallee).site
      (.trapped enclosingCall.saved enclosingCall.continuation)).toLime
    ⟨(outerStore trappingCallee).mapCode V1.Func.toLime, callParent,
      [.source (.intConst .i32 11), .trap, .source (.intBinOp .i32 .add)]⟩ := by
  rw [Enclosing.v1_to_lime]
  exact Enclosing.lime_sound (Enclosing.guard_to_lime (enclosingCallGuard trappingCallee failingGuard))
    discardContinuationCall

private def callTrapStart : Enclosing.State enclosingCall (outer trappingCallee).site :=
  .active (.label (.trapped saved (later trappingCallee)))

example {target : Core.Config Unit}
    (path : Core.Steps Profile.spec noHost
      (Enclosing.v1Config (outerStore trappingCallee) enclosingCall (outer trappingCallee).site callTrapStart).toLime.toCore target) :
    ∃ phase, Enclosing.Unwinding enclosingCall (outer trappingCallee).site phase ∧
      target = (Enclosing.v1Config (outerStore trappingCallee) enclosingCall
        (outer trappingCallee).site phase).toLime.toCore := by
  have g := Enclosing.guard_to_lime (enclosingCallGuard trappingCallee failingGuard)
  rw [Enclosing.v1_to_lime, Enclosing.lime_to_core g] at path
  obtain ⟨phase, run, _, eq⟩ := (Enclosing.core_run_iff (Enclosing.guard_to_core g) (enclosingCallTyped trappingCallee)
    (a := callTrapStart) ⟨trivial, trivial⟩).mp path
  exact ⟨phase, Enclosing.trap_bypasses (.active (.label _ _) trivial) run,
    by rw [Enclosing.v1_to_lime, Enclosing.lime_to_core g, eq]⟩

open DirectSequence.Enclosing

private def recipient : Frame := ⟨[i32 41], {}⟩

private theorem framedSuccess :
    Framed.Runs enclosingCall (outer firstCallee) (.label (.active .call)) (.done (.values [i32 28])) :=
  Framed.finish_run callContinued (.values _) rfl

private theorem framedTrap :
    Framed.Runs enclosingCall (outer trappingCallee) (.label (.active .call)) (.done .trap) :=
  Framed.finish_run callTrap .trap trivial

example : V1.Execution.Steps CallFrame.v1NoHost
    (Framed.v1Config (outerStore firstCallee) recipient enclosingCall (outer firstCallee).site (.label (.active .call)))
    ⟨outerStore firstCallee, recipient, [.frame 1 callParent [.source (.intConst .i32 28)]]⟩ := by
  have atExit := (Framed.label_run callContinued).tail (Framed.fact (.leaveLabel (.values [i32 28])))
  exact (Framed.v1_run_iff (enclosingCallGuard firstCallee regularGuard) (enclosingCallTyped firstCallee)
    (a := .label (.active .call)) ⟨trivial, trivial⟩).mpr ⟨_, atExit, rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (Framed.v1Config (outerStore firstCallee) recipient enclosingCall (outer firstCallee).site (.label (.active .call))).toLime
    ⟨(outerStore firstCallee).mapCode V1.Func.toLime, recipient, [.source (.intConst .i32 28)]⟩ := by
  rw [Framed.v1_to_lime]
  have g := Enclosing.guard_to_lime (enclosingCallGuard firstCallee regularGuard)
  exact (Framed.lime_run_iff g (enclosingCallTyped firstCallee)
    (a := .label (.active .call)) ⟨trivial, trivial⟩).mpr ⟨_, framedSuccess, rfl, rfl⟩

example : Core.Steps Profile.spec noHost
    (Framed.v1Config (outerStore trappingCallee) recipient enclosingCall (outer trappingCallee).site
      (.label (.active .call))).toLime.toCore
    ⟨((outerStore trappingCallee).mapCode V1.Func.toLime).toCore, recipient.toCore, [.trap]⟩ := by
  have g := Enclosing.guard_to_lime (enclosingCallGuard trappingCallee failingGuard)
  rw [Framed.v1_to_lime, Framed.lime_to_core recipient g]
  exact (Framed.core_run_iff (Enclosing.guard_to_core g) (enclosingCallTyped trappingCallee)
    (a := .label (.active .call)) ⟨trivial, trivial⟩).mpr ⟨_, framedTrap, trivial, rfl⟩

example {target : Core.Config Unit}
    (path : Core.Steps Profile.spec noHost
      (Framed.v1Config (outerStore trappingCallee) recipient enclosingCall (outer trappingCallee).site
        (.label callTrapStart)).toLime.toCore target) :
    ∃ phase, Framed.Unwinding enclosingCall (outer trappingCallee).site phase ∧
      target = (Framed.v1Config (outerStore trappingCallee) recipient enclosingCall
        (outer trappingCallee).site phase).toLime.toCore := by
  have g := Enclosing.guard_to_lime (enclosingCallGuard trappingCallee failingGuard)
  rw [Framed.v1_to_lime, Framed.lime_to_core recipient g] at path
  obtain ⟨phase, run, _, eq⟩ := (Framed.core_run_iff (Enclosing.guard_to_core g) (enclosingCallTyped trappingCallee)
    (a := .label callTrapStart) ⟨trivial, trivial⟩).mp path
  exact ⟨phase, Framed.trap_unwinds (.label (.active (.label _ _) trivial)) run,
    by rw [Framed.v1_to_lime, Framed.lime_to_core recipient g, eq]⟩

private def twoResults : Enclosing.Context :=
  ⟨{ callSequence with results := [.int .i64, int32] }, [Value.int .i64 11], []⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (Framed.limeConfig ((outerStore firstCallee).mapCode V1.Func.toLime) recipient twoResults
      (outer firstCallee).site (.label (.active .call)))
    ⟨(outerStore firstCallee).mapCode V1.Func.toLime, recipient,
      [.source (.intConst .i64 11), .source (.intConst .i32 17)]⟩ := by
  have guarded := Enclosing.guard_to_lime (enclosingCallGuard firstCallee regularGuard)
  have g : Enclosing.LimeGuard ((outerStore firstCallee).mapCode V1.Func.toLime) twoResults (outer firstCallee) :=
    ⟨guarded.invocation, ⟨guarded.continuation.readOnly, guarded.continuation.typed,
      guarded.continuation.resolves, guarded.continuation.allocated⟩⟩
  have typed : twoResults.Typed (outer firstCallee) := rfl
  have path := Framed.finish_run (Enclosing.invoke_run (ctx := twoResults) outerNormal)
    (.values [Value.int .i64 11, i32 17]) rfl
  exact (Framed.lime_run_iff g typed (a := .label (.active .call)) ⟨trivial, trivial⟩).mpr
    ⟨_, path, rfl, rfl⟩

example : ¬ Framed.Admitted (ctx := twoResults) (site := (outer firstCallee).site)
    (.exit (.values [i32 17, Value.int .i64 11])) := by
  intro wrongOrder
  change [int32, NumType.int .i64] = [NumType.int .i64, int32] at wrongOrder
  cases wrongOrder

open DirectSequence.Enclosing.Framed

private def sourceCaller : Frame := { recipient with module := { funcs := [⟨3⟩] } }

private def sourceDecl (results : List NumType) : Declaration :=
  ⟨callParent.module, ⟨0⟩, [int32], [int32], results⟩

private def sourceCall (fn : CallFrame.Callee) : Source.Invocation :=
  ⟨⟨⟨0⟩, ⟨3⟩, sourceDecl [int32]⟩,
    ⟨outer fn, [i32 11], callSequence.targets, [.call continuationTarget, .numeric (.bin .i32 .add)]⟩, [i32 99]⟩

private def sourceMany : Source.Invocation :=
  ⟨⟨⟨0⟩, ⟨3⟩, sourceDecl [.int .i64, int32]⟩,
    ⟨outer firstCallee, [Value.int .i64 11], callSequence.targets, []⟩, [i32 99]⟩

private def sourceStore (fn : CallFrame.Callee) (invocation : Source.Invocation) : V1.Execution.Store Unit :=
  { outerStore fn with funcs := (outerStore fn).funcs ++
    [.wasm invocation.target.declaration.type invocation.target.declaration.module invocation.body.v1Func] }

private theorem extendedGuard (fn : CallFrame.Callee) (invocation : Source.Invocation) {ctx : Enclosing.Context}
    (g : Enclosing.V1Guard (outerStore fn) ctx (outer fn)) :
    Enclosing.V1Guard (sourceStore fn invocation) ctx (outer fn) := by
  have keep {addr : Nat} {value : Execution.Runtime.FuncInst V1.Func Unit}
      (found : (outerStore fn).funcs[addr]? = some value) : (sourceStore fn invocation).funcs[addr]? = some value := by
    change ((outerStore fn).funcs ++ _)[addr]? = _
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1, found]
  exact ⟨⟨g.invocation.toLookups, keep g.invocation.allocated,
    ⟨g.invocation.body.readOnly, g.invocation.body.typed, g.invocation.body.resolves,
      fun i => keep (g.invocation.body.allocated i)⟩⟩,
    ⟨g.continuation.readOnly, g.continuation.typed, g.continuation.resolves,
      fun i => keep (g.continuation.allocated i)⟩⟩

private theorem sourceGuard (fn : CallFrame.Callee)
    (g : Enclosing.V1Guard (outerStore fn) enclosingCall (outer fn)) :
    Source.V1Guard (sourceStore fn (sourceCall fn)) sourceCaller (sourceCall fn) :=
  ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl, Nat.le_refl 1, extendedGuard fn (sourceCall fn) g⟩

private def rankTable (fn : CallFrame.Callee) (call : Source.Invocation) (innerRank : Nat) : Ranked.Table :=
  let inner := call.body.invocation.site.callTarget
  ⟨[some ⟨(Ranked.leafTarget ⟨⟨0⟩, ⟨0⟩, fn⟩).declaration, 0, []⟩,
    some ⟨(Ranked.leafTarget ⟨⟨1⟩, ⟨1⟩, secondCallee⟩).declaration, 0, []⟩,
    some ⟨inner.declaration, innerRank, call.body.invocation.site.targets.map Ranked.leafTarget⟩,
    some ⟨call.target.declaration, 2, inner :: call.body.targets.map Ranked.leafTarget⟩]⟩

private theorem successRanks : (rankTable firstCallee (sourceCall firstCallee) 1).checkInvocation
    (sourceCall firstCallee) = true := rfl

private theorem trapRanks : (rankTable trappingCallee (sourceCall trappingCallee) 1).checkInvocation
    (sourceCall trappingCallee) = true := rfl

example : (rankTable firstCallee (sourceCall firstCallee) 2).check = false := rfl
example : (rankTable firstCallee (sourceCall firstCallee) 3).check = false := rfl

-- The generic graph checker can accept missing edges. The body check rejects
-- that same table when the actual checked code has a call at the missing edge.
private def omittedTargets : Ranked.Table :=
  ⟨(rankTable firstCallee (sourceCall firstCallee) 1).entries.modify 2
    (Option.map fun entry => { entry with targets := [] })⟩

example : omittedTargets.check = true := rfl
example : omittedTargets.checkInvocation (sourceCall firstCallee) = false := rfl

private def nestedEntry (fn : CallFrame.Callee) : Source.State (sourceCall fn) :=
  .framed (.label (.active (.label (entered fn))))

private theorem reachesNested (fn : CallFrame.Callee) (count : fn.params.length = 1) (locals : fn.locals = []) :
    Source.Runs (sourceCall fn) .call (nestedEntry fn) :=
  Source.enter_run (Framed.label_run (Enclosing.invoke_run (fromCall fn (firstEnters fn count locals))))

example : Ranked.frames (nestedEntry firstCallee) = [⟨3⟩, ⟨2⟩, ⟨0⟩] := rfl

example : ([2, 1, 0] : List Nat).IsChain (fun caller callee => callee < caller) := by
  have outer := List.isChain_cons_cons.mp (Ranked.Table.ranks_of_check successRanks (nestedEntry firstCallee))
  have inner := List.isChain_cons_cons.mp outer.2
  exact List.isChain_cons_cons.mpr ⟨outer.1, List.isChain_cons_cons.mpr ⟨inner.1, .singleton _⟩⟩

private theorem nestedReturns : Source.Runs (sourceCall firstCallee) (nestedEntry firstCallee)
    (.framed (.done (.values [i32 28]))) := by
  have outerReturned := outerFinishes firstCallee normalAfterEntry (.values _) rfl
  have resumed := Enclosing.invoke_run (ctx := enclosingCall) outerReturned
  have resolved := resumed.tail (Enclosing.resume (fact (.resolve continuationTarget [i32 11] [i32 17] afterCall rfl)))
  exact Source.framed_run (Framed.finish_run (resumeAfterResolve resolved) (.values _) rfl)

private theorem nestedUnwinds : Source.Runs (sourceCall trappingCallee) (nestedEntry trappingCallee)
    (.framed (.done .trap)) := by
  have outerUnwound := outerFinishes trappingCallee trapAfterEntry .trap trivial
  have unwound := unwindAfterTrap (Enclosing.invoke_run outerUnwound)
  exact Source.framed_run (Framed.finish_run unwound .trap trivial)

example : V1.Execution.Steps CallFrame.v1NoHost
    (Source.v1Config (sourceStore firstCallee (sourceCall firstCallee)) sourceCaller (sourceCall firstCallee) .call)
    (Source.v1Config (sourceStore firstCallee (sourceCall firstCallee)) sourceCaller (sourceCall firstCallee)
      (nestedEntry firstCallee)) :=
  (Ranked.v1_run_iff successRanks (sourceGuard firstCallee (enclosingCallGuard firstCallee regularGuard))
    (a := .call) trivial).mpr
    ⟨_, reachesNested firstCallee rfl rfl, ⟨trivial, ⟨trivial, ⟨rfl, rfl⟩, rfl⟩⟩, rfl,
      Ranked.Table.nesting_of_check successRanks _⟩

example : V1.Execution.Step CallFrame.v1NoHost
    (Source.v1Config (sourceStore firstCallee (sourceCall firstCallee)) sourceCaller (sourceCall firstCallee) .invoke)
    ⟨sourceStore firstCallee (sourceCall firstCallee), sourceCaller, [.frame 1 callParent [.label 1 []
      [.source (.intConst .i32 11), .source (.intConst .i32 5), .source (.intConst .i32 2), .source (.intConst .i32 3),
        .source (.call ⟨0⟩), .source (.call ⟨1⟩), .source (.intBinOp .i32 .add)]]]⟩ :=
  Source.v1_sound (sourceGuard firstCallee (enclosingCallGuard firstCallee regularGuard)) (Source.fact .enter)

example : V1.Execution.Steps CallFrame.v1NoHost
    ⟨sourceStore firstCallee (sourceCall firstCallee), sourceCaller, [.source (.intConst .i32 99), .source (.call ⟨0⟩)]⟩
    ⟨sourceStore firstCallee (sourceCall firstCallee), sourceCaller, [.source (.intConst .i32 28)]⟩ :=
  (Ranked.v1_run_iff successRanks (sourceGuard firstCallee (enclosingCallGuard firstCallee regularGuard))
    (a := .call) trivial).mpr
    ⟨_, (reachesNested firstCallee rfl rfl).trans nestedReturns, rfl, rfl, .nil⟩

example : Core.Steps Profile.spec noHost
    (Source.v1Config (sourceStore trappingCallee (sourceCall trappingCallee))
      sourceCaller (sourceCall trappingCallee) .call).toLime.toCore
    ⟨((sourceStore trappingCallee (sourceCall trappingCallee)).mapCode V1.Func.toLime).toCore,
      sourceCaller.toCore, [.trap]⟩ := by
  have g := Source.guard_to_lime (sourceGuard trappingCallee (enclosingCallGuard trappingCallee failingGuard))
  rw [Source.v1_to_lime, Source.lime_to_core g]
  exact (Ranked.core_run_iff trapRanks (Source.guard_to_core g) (a := .call) trivial).mpr
    ⟨_, (reachesNested trappingCallee rfl rfl).trans nestedUnwinds, trivial, rfl, .nil⟩

private theorem sourceManyGuard :
    Source.LimeGuard ((sourceStore firstCallee sourceMany).mapCode V1.Func.toLime) sourceCaller sourceMany := by
  have base := enclosingCallGuard firstCallee regularGuard
  have body : Enclosing.V1Guard (outerStore firstCallee) twoResults (outer firstCallee) :=
    ⟨base.invocation, ⟨base.continuation.readOnly, base.continuation.typed,
      base.continuation.resolves, base.continuation.allocated⟩⟩
  exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl, Enclosing.guard_to_lime (extendedGuard firstCallee sourceMany body)⟩

private theorem sourceManyRun : Source.Runs sourceMany .call
    (.framed (.done (.values [Value.int .i64 11, i32 17]))) :=
  Source.enter_run (Framed.finish_run (Enclosing.invoke_run (ctx := twoResults) outerNormal) (.values _) rfl)

example : Lime1.Execution.Steps CallFrame.limeNoHost
    ⟨(sourceStore firstCallee sourceMany).mapCode V1.Func.toLime, sourceCaller,
      [.source (.intConst .i32 99), .source (.call ⟨0⟩)]⟩
    ⟨(sourceStore firstCallee sourceMany).mapCode V1.Func.toLime, sourceCaller,
      [.source (.intConst .i64 11), .source (.intConst .i32 17)]⟩ :=
  (Ranked.lime_run_iff (table := rankTable firstCallee sourceMany 1) rfl sourceManyGuard (a := .call) trivial).mpr
    ⟨_, sourceManyRun, rfl, rfl, .nil⟩

example : Core.Steps Profile.spec noHost
    ⟨((sourceStore firstCallee sourceMany).mapCode V1.Func.toLime).toCore, sourceCaller.toCore,
      [.plain (.intConst .i32 99), .plain (.call ⟨0⟩)]⟩
    ⟨((sourceStore firstCallee sourceMany).mapCode V1.Func.toLime).toCore, sourceCaller.toCore,
      [.plain (.intConst .i64 11), .plain (.intConst .i32 17)]⟩ :=
  (Ranked.core_run_iff (table := rankTable firstCallee sourceMany 1) rfl (Source.guard_to_core sourceManyGuard)
    (a := .call) trivial).mpr ⟨_, sourceManyRun, rfl, rfl, .nil⟩

example {s : V1.Execution.Store Unit} : ¬ Source.V1Guard s sourceCaller sourceMany := by
  intro g
  have scalar : 2 ≤ 1 := g.scalarResult
  omega

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence
