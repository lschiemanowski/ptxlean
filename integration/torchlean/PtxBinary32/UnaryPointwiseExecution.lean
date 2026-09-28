import PtxBinary32.UnaryPointwiseControl

/-! A chosen lane schedule realizes every permitted elementwise result. This
is a separate existence witness; candidate-execution correctness is universal. -/
namespace Ptx.Scalar.UnaryPointwise
open ParallelUnary

private theorem supported : ParallelUnary.Supported target := by norm_num [ParallelUnary.Supported,target]

@[simp] theorem input_install (s : ParallelUnary.State n) (t : Fin n) (next : Scalar.State) (halted : Bool) :
    ParallelUnary.input (ParallelUnary.install s t next halted) t=next := by
  simp [ParallelUnary.input,ParallelUnary.install]

@[simp] theorem install_install (s : ParallelUnary.State n) (t : Fin n)
    (a b : Scalar.State) (ha hb : Bool) :
    ParallelUnary.install (ParallelUnary.install s t a ha) t b hb=ParallelUnary.install s t b hb := by
  simp [ParallelUnary.install,Function.update_idem]

def LaneResult (_op : Op) (common : Nat) (s final : ParallelUnary.State n) (t : Fin n) (out : Word)
    (events : List (ParallelUnary.Event n)) : Prop :=
  final.global=s.global.set t.val out ∧ (final.lanes t).halted=true ∧
  (∀u, u≠t → final.lanes u=s.lanes u) ∧
  (∀event∈events, ∀effect, event.memory=some effect → effect.kind=.load →
    (effect.address=pointer t.val ∧ effect.value=s.global[t.val]!) ∨
    (effect.address=pointer common ∧ effect.value=s.global[common]!))

theorem normalize_lane (s : ParallelUnary.State n) (t : Fin n) (common : Nat) (out : Word)
    (pc : (s.lanes t).scalar.pc=0) (live : (s.lanes t).halted=false)
    (own : (s.lanes t).scalar.addrs 0=pointer t.val)
    (shared : (s.lanes t).scalar.addrs 1=pointer common)
    (va : SoftmaxMemory.ValidIndex s.global t.val) (vb : SoftmaxMemory.ValidIndex s.global common)
    (allowed : Result .normalize s.global[t.val]! s.global[common]! out) :
    ∃events final, ParallelUnary.ConcreteRuns target (program .normalize) s events final ∧
      LaneResult .normalize common s final t out events := by
  obtain ⟨inv,h0,h1⟩ := allowed
  let l0 := ParallelUnary.input s t
  let l1 := SoftmaxMemory.write l0 0 s.global[t.val]!
  let l2 := SoftmaxMemory.write l1 1 s.global[common]!
  let l3 := SoftmaxMemory.write l2 2 inv
  let l4 := SoftmaxMemory.write l3 2 out
  let l5 := SoftmaxMemory.save l4 t.val
  let p1 := ParallelUnary.install s t l1 false
  let p2 := ParallelUnary.install s t l2 false
  let p3 := ParallelUnary.install s t l3 false
  let p4 := ParallelUnary.install s t l4 false
  let p5 := ParallelUnary.install s t l5 false
  let final := ParallelUnary.install s t l5 true
  let e0 := Scalar.occurrence l0 (.plain (.load 0 (.reg 0))) true (some ⟨.load,pointer t.val,s.global[t.val]!⟩)
  let e1 := Scalar.occurrence l1 (.plain (.load 1 (.reg 1))) true (some ⟨.load,pointer common,s.global[common]!⟩)
  let e2 := Scalar.Reciprocal.occurrence l2 (Normalize.reciprocal 1 2) true
  let e3 := Scalar.Binary32.occurrence l3 (Normalize.multiply 0 2) true
  let e4 := Scalar.occurrence l4 (.plain (.store (.reg 0) (.reg 2))) true (some ⟨.store,pointer t.val,out⟩)
  let e5 := Scalar.occurrence l5 (.plain .exit) true
  have v0 : Scalar.eval none (.plain (.load 0 (.reg 0))) l0=.next l1 e0 := by
    simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,e0,l0,l1,SoftmaxMemory.write,ParallelUnary.input,own,pointer,SoftmaxMemory.address_index _ _ va]
  have v1 : Scalar.eval none (.plain (.load 1 (.reg 1))) l1=.next l2 e1 := by
    simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,e1,l0,l1,l2,SoftmaxMemory.write,ParallelUnary.input,shared,pointer,SoftmaxMemory.address_index _ _ vb]
  have v2 : Scalar.Reciprocal.Eval (Normalize.reciprocal 1 2) l2 l3 e2 := by
    apply Scalar.Reciprocal.Eval.executed rfl
    simpa [l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,Normalize.reciprocal] using h0
  have v3 : Scalar.Binary32.Eval (Normalize.multiply 0 2) l3 l4 e3 := by
    apply Scalar.Binary32.Eval.executed rfl
    simpa [l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,Normalize.multiply] using h1
  have v4 : Scalar.eval none (.plain (.store (.reg 0) (.reg 2))) l4=.next l5 e4 := by
    simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,e4,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,own,pointer,SoftmaxMemory.address_index _ _ va]
  have v5 : Scalar.eval none (.plain .exit) l5=.halted l5 e5 := rfl
  have step0 : ParallelUnary.Step target (program .normalize) none t s p1 (.scalar t e0) := by
    refine ⟨supported,?_,ownLoad,?_,?_⟩
    · simp [live]
    · simp [program,body,arithmetic,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.scalarNext (s:=s) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v0))
  have step1 : ParallelUnary.Step target (program .normalize) none t p1 p2 (.scalar t e1) := by
    refine ⟨supported,?_,commonLoad,?_,?_⟩
    · simp [p1,ParallelUnary.install]
    · simp [program,body,arithmetic,p1,l0,l1,SoftmaxMemory.write,ParallelUnary.input,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.scalarNext (s:=p1) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v1))
  have step2 : ParallelUnary.Step target (program .normalize) none t p2 p3 (.reciprocal t e2) := by
    refine ⟨supported,?_,.reciprocal (Normalize.reciprocal 1 2),?_,?_⟩
    · simp [p2,ParallelUnary.install]
    · simp [program,body,arithmetic,p2,l0,l1,l2,SoftmaxMemory.write,ParallelUnary.input,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.reciprocal (s:=p2) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v2))
  have step3 : ParallelUnary.Step target (program .normalize) none t p3 p4 (.binary t e3) := by
    refine ⟨supported,?_,.binary (Normalize.multiply 0 2),?_,?_⟩
    · simp [p3,ParallelUnary.install]
    · simp [program,body,arithmetic,p3,l0,l1,l2,l3,SoftmaxMemory.write,ParallelUnary.input,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.binary (s:=p3) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v3))
  have step4 : ParallelUnary.Step target (program .normalize) none t p4 p5 (.scalar t e4) := by
    refine ⟨supported,?_,ownStore,?_,?_⟩
    · simp [p4,ParallelUnary.install]
    · simp [program,body,arithmetic,p4,l0,l1,l2,l3,l4,SoftmaxMemory.write,ParallelUnary.input,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.scalarNext (s:=p4) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v4))
  have step5 : ParallelUnary.Step target (program .normalize) none t p5 final (.scalar t e5) := by
    refine ⟨supported,?_,exitInstr,?_,?_⟩
    · simp [p5,ParallelUnary.install]
    · simp [program,body,arithmetic,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.scalarHalted (s:=p5) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v5))
  refine ⟨[.scalar t e0,.scalar t e1,.reciprocal t e2,.binary t e3,.scalar t e4,.scalar t e5],final,?_,?_⟩
  · exact .cons step0 (.cons step1 (.cons step2 (.cons step3 (.cons step4 (.cons step5 (.nil))))))
  · refine ⟨?_,?_,?_,?_⟩
    · simp [final,ParallelUnary.install,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update]
    · simp [final,ParallelUnary.install]
    · intro u ne; simp [final,ParallelUnary.install,Function.update,ne]
    · intro event member effect memory kind
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [ParallelUnary.Event.memory,e0,e1,e4,e5,Scalar.occurrence] at memory
      all_goals subst effect
      all_goals simp_all

theorem shifted_lane (s : ParallelUnary.State n) (t : Fin n) (common : Nat) (out : Word)
    (pc : (s.lanes t).scalar.pc=0) (live : (s.lanes t).halted=false)
    (own : (s.lanes t).scalar.addrs 0=pointer t.val)
    (shared : (s.lanes t).scalar.addrs 1=pointer common)
    (va : SoftmaxMemory.ValidIndex s.global t.val) (vb : SoftmaxMemory.ValidIndex s.global common)
    (allowed : Result .shifted s.global[t.val]! s.global[common]! out) :
    ∃events final, ParallelUnary.ConcreteRuns target (program .shifted) s events final ∧
      LaneResult .shifted common s final t out events := by
  obtain ⟨negative,shifted,product,h0,h1,h2,h3⟩ := allowed
  let l0 := ParallelUnary.input s t
  let l1 := SoftmaxMemory.write l0 0 s.global[t.val]!
  let l2 := SoftmaxMemory.write l1 1 s.global[common]!
  let l3 := SoftmaxMemory.write l2 2 negative
  let l4 := SoftmaxMemory.write l3 2 shifted
  let l5 := SoftmaxMemory.write l4 2 product
  let l6 := SoftmaxMemory.write l5 2 out
  let l7 := SoftmaxMemory.save l6 t.val
  let p1 := ParallelUnary.install s t l1 false
  let p2 := ParallelUnary.install s t l2 false
  let p3 := ParallelUnary.install s t l3 false
  let p4 := ParallelUnary.install s t l4 false
  let p5 := ParallelUnary.install s t l5 false
  let p6 := ParallelUnary.install s t l6 false
  let p7 := ParallelUnary.install s t l7 false
  let final := ParallelUnary.install s t l7 true
  let e0 := Scalar.occurrence l0 (.plain (.load 0 (.reg 0))) true (some ⟨.load,pointer t.val,s.global[t.val]!⟩)
  let e1 := Scalar.occurrence l1 (.plain (.load 1 (.reg 1))) true (some ⟨.load,pointer common,s.global[common]!⟩)
  let e2 := Scalar.Binary32.occurrence l2 (ShiftedExp.negate 1 2) true
  let e3 := Scalar.Binary32.occurrence l3 (ShiftedExp.shift 0 2) true
  let e4 := Scalar.Binary32.occurrence l4 (ShiftedExp.convert 2) true
  let e5 := Scalar.Exponential.occurrence l5 (ShiftedExp.exponential 2) true
  let e6 := Scalar.occurrence l6 (.plain (.store (.reg 0) (.reg 2))) true (some ⟨.store,pointer t.val,out⟩)
  let e7 := Scalar.occurrence l7 (.plain .exit) true
  have v0 : Scalar.eval none (.plain (.load 0 (.reg 0))) l0=.next l1 e0 := by
    simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,e0,l0,l1,SoftmaxMemory.write,ParallelUnary.input,own,pointer,SoftmaxMemory.address_index _ _ va]
  have v1 : Scalar.eval none (.plain (.load 1 (.reg 1))) l1=.next l2 e1 := by
    simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,e1,l0,l1,l2,SoftmaxMemory.write,ParallelUnary.input,shared,pointer,SoftmaxMemory.address_index _ _ vb]
  have v2 : Scalar.Binary32.Eval (ShiftedExp.negate 1 2) l2 l3 e2 := by
    apply Scalar.Binary32.Eval.executed rfl
    simpa [l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ShiftedExp.negate] using h0
  have v3 : Scalar.Binary32.Eval (ShiftedExp.shift 0 2) l3 l4 e3 := by
    apply Scalar.Binary32.Eval.executed rfl
    simpa [l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ShiftedExp.shift] using h1
  have v4 : Scalar.Binary32.Eval (ShiftedExp.convert 2) l4 l5 e4 := by
    apply Scalar.Binary32.Eval.executed rfl
    simpa [l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ShiftedExp.convert] using h2
  have v5 : Scalar.Exponential.Eval (ShiftedExp.exponential 2) l5 l6 e5 := by
    apply Scalar.Exponential.Eval.executed rfl
    simpa [l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ShiftedExp.exponential] using h3
  have v6 : Scalar.eval none (.plain (.store (.reg 0) (.reg 2))) l6=.next l7 e6 := by
    simp [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,e6,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,own,pointer,SoftmaxMemory.address_index _ _ va]
  have v7 : Scalar.eval none (.plain .exit) l7=.halted l7 e7 := rfl
  have step0 : ParallelUnary.Step target (program .shifted) none t s p1 (.scalar t e0) := by
    refine ⟨supported,?_,ownLoad,?_,?_⟩
    · simp [live]
    · simp [program,body,arithmetic,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.scalarNext (s:=s) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v0))
  have step1 : ParallelUnary.Step target (program .shifted) none t p1 p2 (.scalar t e1) := by
    refine ⟨supported,?_,commonLoad,?_,?_⟩
    · simp [p1,ParallelUnary.install]
    · simp [program,body,arithmetic,p1,l0,l1,SoftmaxMemory.write,ParallelUnary.input,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.scalarNext (s:=p1) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v1))
  have step2 : ParallelUnary.Step target (program .shifted) none t p2 p3 (.binary t e2) := by
    refine ⟨supported,?_,.binary (ShiftedExp.negate 1 2),?_,?_⟩
    · simp [p2,ParallelUnary.install]
    · simp [program,body,arithmetic,p2,l0,l1,l2,SoftmaxMemory.write,ParallelUnary.input,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.binary (s:=p2) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v2))
  have step3 : ParallelUnary.Step target (program .shifted) none t p3 p4 (.binary t e3) := by
    refine ⟨supported,?_,.binary (ShiftedExp.shift 0 2),?_,?_⟩
    · simp [p3,ParallelUnary.install]
    · simp [program,body,arithmetic,p3,l0,l1,l2,l3,SoftmaxMemory.write,ParallelUnary.input,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.binary (s:=p3) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v3))
  have step4 : ParallelUnary.Step target (program .shifted) none t p4 p5 (.binary t e4) := by
    refine ⟨supported,?_,.binary (ShiftedExp.convert 2),?_,?_⟩
    · simp [p4,ParallelUnary.install]
    · simp [program,body,arithmetic,p4,l0,l1,l2,l3,l4,SoftmaxMemory.write,ParallelUnary.input,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.binary (s:=p4) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v4))
  have step5 : ParallelUnary.Step target (program .shifted) none t p5 p6 (.exponential t e5) := by
    refine ⟨supported,?_,.exponential (ShiftedExp.exponential 2),?_,?_⟩
    · simp [p5,ParallelUnary.install]
    · simp [program,body,arithmetic,p5,l0,l1,l2,l3,l4,l5,SoftmaxMemory.write,ParallelUnary.input,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.exponential (s:=p5) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v5))
  have step6 : ParallelUnary.Step target (program .shifted) none t p6 p7 (.scalar t e6) := by
    refine ⟨supported,?_,ownStore,?_,?_⟩
    · simp [p6,ParallelUnary.install]
    · simp [program,body,arithmetic,p6,l0,l1,l2,l3,l4,l5,l6,SoftmaxMemory.write,ParallelUnary.input,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.scalarNext (s:=p6) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v6))
  have step7 : ParallelUnary.Step target (program .shifted) none t p7 final (.scalar t e7) := by
    refine ⟨supported,?_,exitInstr,?_,?_⟩
    · simp [p7,ParallelUnary.install]
    · simp [program,body,arithmetic,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,ParallelUnary.install,pc,ownLoad,commonLoad,ownStore,exitInstr]
    · simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using
        (ParallelUnary.Exec.scalarHalted (s:=p7) (thread:=t) (candidate:=none) (by simpa [final,p1,p2,p3,p4,p5,p6,p7,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update,Scalar.Operand32.eval,ParallelUnary.install,ParallelUnary.setLane,Function.update_idem,pc,live,ownLoad,commonLoad,ownStore,exitInstr] using v7))
  refine ⟨[.scalar t e0,.scalar t e1,.binary t e2,.binary t e3,.binary t e4,.exponential t e5,.scalar t e6,.scalar t e7],final,?_,?_⟩
  · exact .cons step0 (.cons step1 (.cons step2 (.cons step3 (.cons step4 (.cons step5 (.cons step6 (.cons step7 (.nil))))))))
  · refine ⟨?_,?_,?_,?_⟩
    · simp [final,ParallelUnary.install,l0,l1,l2,l3,l4,l5,l6,l7,SoftmaxMemory.write,SoftmaxMemory.save,ParallelUnary.input,Scalar.update]
    · simp [final,ParallelUnary.install]
    · intro u ne; simp [final,ParallelUnary.install,Function.update,ne]
    · intro event member effect memory kind
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [ParallelUnary.Event.memory,e0,e1,e6,e7,Scalar.occurrence] at memory
      all_goals subst effect
      all_goals simp_all

theorem lane_realize (op : Op) (s : ParallelUnary.State n) (t : Fin n) (common : Nat) (out : Word)
    (pc : (s.lanes t).scalar.pc=0) (live : (s.lanes t).halted=false)
    (own : (s.lanes t).scalar.addrs 0=pointer t.val)
    (shared : (s.lanes t).scalar.addrs 1=pointer common)
    (va : SoftmaxMemory.ValidIndex s.global t.val) (vb : SoftmaxMemory.ValidIndex s.global common)
    (allowed : Result op s.global[t.val]! s.global[common]! out) :
    ∃events final, ParallelUnary.ConcreteRuns target (program op) s events final ∧
      LaneResult op common s final t out events := by
  cases op with
  | shifted => exact shifted_lane s t common out pc live own shared va vb allowed
  | normalize => exact normalize_lane s t common out pc live own shared va vb allowed

/-- The constructive schedule's actual load occurrences read original words. -/
def InitialReads (before : List Word) (events : List (ParallelUnary.Event n)) : Prop :=
  ∀event∈events, ∀effect, event.memory=some effect → effect.kind=.load →
    effect.value=before[effect.address.toNat/4]!

private structure Partial (op : Op) (common : Nat) (before after : List Word)
    (seeds : Fin n → Scalar.State) (k : Nat) (events : List (ParallelUnary.Event n))
    (state : ParallelUnary.State n) : Prop where
  run : ParallelUnary.ConcreteRuns target (program op) (initial common before seeds) events state
  length : state.global.length=before.length
  cells : ∀i, state.global[i]?=if i<k then after[i]? else before[i]?
  lanes : ∀t : Fin n, (if t.val<k then (state.lanes t).halted=true
    else state.lanes t=(initial common before seeds).lanes t)
  reads : InitialReads before events

/-- Prescribed outcomes, including every allowed approximate-exponential choice,
are realized by finishing one lane at a time. The universal theorem permits all
admitted interleavings, independently of this particular existence schedule. -/
theorem realize_with_seeds (op : Op) (n common : Nat) (before after : List Word)
    (seeds : Fin n → Scalar.State) (bounds : Bounds n common before)
    (spec : Spec op n common before after) :
    ∃events final, ParallelUnary.ConcreteRuns target (program op) (initial common before seeds) events final ∧
      final.global=after ∧ (∀t, (final.lanes t).halted=true) ∧ InitialReads before events := by
  have construct : ∀k, k≤n → ∃events state, Partial op common before after seeds k events state := by
    intro k hk
    induction k with
    | zero =>
      exact ⟨[],initial common before seeds,.nil,rfl,by simp [initial],by simp,by intro e mem; simp at mem⟩
    | succ k ih =>
      obtain ⟨events,state,prior⟩ := ih (by omega)
      let thread : Fin n := ⟨k,by omega⟩
      have lane : state.lanes thread=(initial common before seeds).lanes thread := by
        simpa [thread] using prior.lanes thread
      have inside : k<before.length := by have := bounds.2.2.1; have := bounds.2.2.2.1; omega
      have commonBefore : k≤common := by have := bounds.2.2.1; omega
      have ownValue : state.global[k]! = before[k]! := by
        apply SoftmaxStorage.bang_eq
        simpa using prior.cells k
      have commonValue : state.global[common]! = before[common]! := by
        apply SoftmaxStorage.bang_eq
        simpa [Nat.not_lt.mpr commonBefore] using prior.cells common
      have va : SoftmaxMemory.ValidIndex state.global thread.val := by
        change k<state.global.length ∧ k<2^62
        rw [prior.length]
        exact ⟨inside,inside.trans bounds.2.2.2.2⟩
      have vb : SoftmaxMemory.ValidIndex state.global common := by
        rw [SoftmaxMemory.ValidIndex,prior.length]
        exact ⟨bounds.2.2.2.1,bounds.2.2.2.1.trans bounds.2.2.2.2⟩
      obtain ⟨nextEvents,next,run,frame⟩ := lane_realize op state thread common after[k]!
        (by simp [lane,initial]) (by simp [lane,initial])
        (by simp [lane,initial,Scalar.update]) (by simp [lane,initial,Scalar.update]) va vb
        (by change Result op state.global[k]! state.global[common]! after[k]!; rw [ownValue,commonValue]; exact spec.2.2 thread)
      refine ⟨events++nextEvents,next,prior.run.append run,?_,?_,?_,?_⟩
      · rw [frame.1,List.length_set,prior.length]
      · intro i
        rw [frame.1]
        by_cases eq : i=k
        · subst i
          have stored : (state.global.set thread.val after[k]!)[k]?=some after[k]! := by
            apply List.getElem?_set_self
            simpa [prior.length] using inside
          rw [stored]
          simp only [Nat.lt_succ_self,ite_true]
          exact (SoftmaxStorage.some_bang after k (by rw [spec.1]; exact inside)).symm
        · rw [List.getElem?_set_ne (by simpa [thread] using Ne.symm eq),prior.cells]
          by_cases lt : i<k <;> simp [lt,show (i<k+1)↔(i<k) by omega]
      · intro u
        by_cases eq : u=thread
        · subst u
          simpa [thread] using frame.2.1
        · rw [frame.2.2.1 u eq]
          have ne : u.val≠k := by intro value; apply eq; apply Fin.ext; exact value
          simpa [show (u.val<k+1)↔(u.val<k) by omega] using prior.lanes u
      · intro event member effect memory load
        rcases List.mem_append.mp member with old | fresh
        · exact prior.reads event old effect memory load
        · obtain (⟨addr,value⟩|⟨addr,value⟩) := frame.2.2.2 event fresh effect memory load
          · rw [addr,value]
            have index : (pointer thread.val).toNat/4=thread.val :=
              (Scalar.addressIndex_ok_iff.mp (SoftmaxMemory.address_index state.global thread.val va)).2.symm
            rw [index]
            exact ownValue
          · rw [addr,value]
            have index : (pointer common).toNat/4=common :=
              (Scalar.addressIndex_ok_iff.mp (SoftmaxMemory.address_index state.global common vb)).2.symm
            rw [index]
            exact commonValue
  obtain ⟨events,final,completed⟩ := construct n le_rfl
  refine ⟨events,final,completed.run,?_,?_,completed.reads⟩
  · apply List.ext_getElem?
    intro i
    rw [completed.cells]
    by_cases small : i<n
    · simp [small]
    · simpa [small] using (spec.2.1 i (by omega)).symm
  · intro t
    simpa [t.isLt] using completed.lanes t

theorem realize (op : Op) (n common : Nat) (before after : List Word)
    (bounds : Bounds n common before) (spec : Spec op n common before after) :
    ∃(seeds : Fin n → Scalar.State) (events : List (ParallelUnary.Event n)) (final : ParallelUnary.State n), ParallelUnary.ConcreteRuns target (program op) (initial common before seeds) events final ∧
      final.global=after ∧ (∀t, (final.lanes t).halted=true) ∧ InitialReads before events := by
  let seeds : Fin n → Scalar.State := fun _ => ⟨0,fun _ => 0,fun _ => 0,fun _ => false,[]⟩
  obtain ⟨events,final,run,memory,halted,reads⟩ := realize_with_seeds op n common before after seeds bounds spec
  exact ⟨seeds,events,final,run,memory,halted,reads⟩

/-- Actual access safety supplies the extent half of the admission certificate's
initial-read contract; the witness supplies the exact initial value half. -/
theorem initial_reads_bounded
    (run : ParallelUnary.ConcreteRuns target (program op) (initial common before seeds) events final)
    (reads : InitialReads before events) :
    ∀t occ effect, ParallelUnary.Event.scalar t occ∈events → occ.memory=some effect → effect.kind=.load →
      effect.address.toNat/4<before.length ∧ effect.value=before[effect.address.toNat/4]! := by
  intro t occ effect member memory load
  have safe := ParallelUnary.runs_memory_safe run.toRuns member memory
  exact ⟨safe.2,reads _ member effect memory load⟩

end Ptx.Scalar.UnaryPointwise
