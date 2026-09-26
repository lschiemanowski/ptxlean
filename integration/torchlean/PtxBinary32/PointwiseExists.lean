import PtxBinary32.PointwiseUniversal
import PtxBinary32.ParallelSegment

namespace Ptx.Scalar.Parallel.Pointwise
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

def Pointers (l : Layout n) (t : Fin n) (state : State n) : Prop :=
  (state.lanes t).scalar.addrs 0=Dense.bytePointer (l.left t) ∧
  (state.lanes t).scalar.addrs 1=Dense.bytePointer (l.right t) ∧
  (state.lanes t).scalar.addrs 2=Dense.bytePointer (l.output t)

def finish (cfg : Config n) (op : Op) (t : Fin n) (state : State n) : State n :=
  (segmentReference cfg t ((program op).take (storePC op+1)) state).1

private theorem checked_address (l : Layout n) (global : List Word) (size : l.prefixWords+n≤global.length)
    (i : Nat) (hi : i<l.prefixWords+n) : Scalar.addressIndex global (Dense.bytePointer i)=.ok i := by
  have fit : 4*i<18446744073709551616 := by have := l.small; omega
  simp [Scalar.addressIndex,Dense.bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,show i<global.length by omega]

theorem lane_regular (cfg : Config n) (op : Op) (l : Layout n) (state : State n) (t : Fin n)
    (ptr : Pointers l t state) (size : l.prefixWords+n≤state.global.length) :
    SegmentRegular cfg t ((program op).take (storePC op+1)) state := by
  have hb : l.output t<l.prefixWords+n := by have := t.isLt; unfold Layout.output; omega
  have h0 := checked_address l state.global size (l.left t) (by have := l.leftBound t; omega)
  have h1 := checked_address l state.global size (l.right t) (by have := l.rightBound t; omega)
  have h2 := checked_address l state.global size (l.output t) hb
  cases op
  all_goals by_cases z : state.global[l.left t]! = 0#32
  all_goals by_cases neg : 2147483648≤(state.global[l.left t]!).toNat
  all_goals simp only [List.getElem!_eq_getElem?_getD] at z neg
  all_goals simp [SegmentRegular,program,body,storePC,localOp,clear,Reference.dispatch,Reference.binary32,
    scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Compare.eval,Scalar.update,setLane,arena,ptr.1,ptr.2.1,ptr.2.2,h0,h1,h2,z,neg]

theorem lane_effect (cfg : Config n) (op : Op) (l : Layout n) (state : State n) (t : Fin n)
    (ptr : Pointers l t state) (size : l.prefixWords+n≤state.global.length) :
    (finish cfg op t state).global=state.global.set (l.output t) (reference op state.global[l.left t]! state.global[l.right t]!) ∧
    (finish cfg op t state).shared=state.shared ∧
    (finish cfg op t state).site=state.site ∧
    (∀ u, u≠t → (finish cfg op t state).lanes u=state.lanes u) := by
  have hb : l.output t<l.prefixWords+n := by have := t.isLt; unfold Layout.output; omega
  have h0 := checked_address l state.global size (l.left t) (by have := l.leftBound t; omega)
  have h1 := checked_address l state.global size (l.right t) (by have := l.rightBound t; omega)
  have h2 := checked_address l state.global size (l.output t) hb
  cases op
  all_goals by_cases z : state.global[l.left t]! = 0#32
  all_goals by_cases neg : 2147483648≤(state.global[l.left t]!).toNat
  all_goals simp only [List.getElem!_eq_getElem?_getD] at z neg
  all_goals simp [finish,segmentReference,program,body,storePC,localOp,clear,Reference.dispatch,Reference.binary32,
    scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Compare.eval,Scalar.update,setLane,arena,ptr.1,ptr.2.1,ptr.2.2,h0,h1,h2,z,neg,
    reference,List.getElem!_eq_getElem?_getD,← gate_bits]
  all_goals intro u ne; simp [Function.update,ne]

def done (cfg : Config n) (op : Op) (t : Fin n) (state : State n) : State n :=
  let last := finish cfg op t state
  setLane last t {last.lanes t with halted := true}

theorem lane_run (cfg : Config n) (eligible : Mixed.Eligible cfg.target) (op : Op) (l : Layout n)
    (state : State n) (t : Fin n) (ptr : Pointers l t state) (size : l.prefixWords+n≤state.global.length)
    (pc : (state.lanes t).scalar.pc=0) (live : (state.lanes t).halted=false)
    (fresh : state.barrier.arrived t=false) :
    ∃ events, ConcreteRuns cfg (program op) state events (done cfg op t state) := by
  have segment := segmentReference_concrete (lane_regular cfg op l state t ptr size)
  have frame := segment.frame
  change ((finish cfg op t state).lanes t).scalar.pc=(state.lanes t).scalar.pc+((program op).take (storePC op+1)).length ∧
    ((finish cfg op t state).lanes t).halted=(state.lanes t).halted ∧ (finish cfg op t state).barrier=state.barrier at frame
  have run := segment.compile (program := program op) (by
    rw [pc]; intro j hj
    have small : j<storePC op+1 := lt_of_lt_of_le hj (List.length_take_le _ _)
    simp [small]) live fresh eligible
  have lastpc : ((finish cfg op t state).lanes t).scalar.pc=storePC op+1 := by
    simpa [pc,List.length_take,length_program] using frame.1
  have fetch : (program op)[storePC op+1]?=some .exit := by cases op <;> rfl
  have step : Step cfg (program op) none t (finish cfg op t state)
      (Reference.dispatch cfg t .exit (finish cfg op t state)) := by
    refine ⟨eligible,?_⟩
    have hl : ((finish cfg op t state).lanes t).halted=false := frame.2.1.trans live
    have hf : (finish cfg op t state).barrier.arrived t=false := by rw [frame.2.2]; exact fresh
    simp only [hl,hf,Bool.false_eq_true,ite_false,lastpc,fetch]
    exact Dispatch.exit
  exact ⟨_,concrete_runs_append run (ConcreteRuns.cons step (ConcreteRuns.nil (s := done cfg op t state)))⟩

/-- During the witness construction only finished lanes have changed. -/
structure Progress (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    (count : Nat) (state : State n) : Prop where
  length : state.global.length=global.length
  sharedEq : state.shared=shared
  barrier : state.barrier=Barrier.reset 0
  pending : ∀ t, count≤t.val → state.lanes t=(initial l global shared seeds).lanes t
  halted : ∀ t, t.val<count → (state.lanes t).halted=true

theorem execution_exists (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    (positive : 0<n) (size : l.prefixWords+n≤global.length) :
    ∃ events final, ConcreteRuns (config positive) (program op) (initial l global shared seeds) events final ∧
      (∀ t, (final.lanes t).halted=true) := by
  have eligible : Mixed.Eligible (config positive).target := by change 94=94 ∧ 70≤70; decide
  have aux : ∀ count, count≤n → ∃ events final,
      ConcreteRuns (config positive) (program op) (initial l global shared seeds) events final ∧
      Progress l global shared seeds count final := by
    intro count limit
    induction count with
    | zero =>
      exact ⟨[],initial l global shared seeds,.nil,rfl,rfl,rfl,fun _ _ => rfl,by intro t h; omega⟩
    | succ count ih =>
      obtain ⟨events,current,run,inv⟩ := ih (by omega)
      let t : Fin n := ⟨count,by omega⟩
      have old := inv.pending t (by rfl)
      have ptr : Pointers l t current := by unfold Pointers; rw [show current.lanes t=(initial l global shared seeds).lanes t from old]; simp [Pointers,initial,seed]
      have currentSize : l.prefixWords+n≤current.global.length := by rw [inv.length]; exact size
      have pc : (current.lanes t).scalar.pc=0 := by rw [old]; rfl
      have live : (current.lanes t).halted=false := by rw [old]; rfl
      have fresh : current.barrier.arrived t=false := by rw [inv.barrier]; rfl
      obtain ⟨added,localRun⟩ := lane_run (config positive) eligible op l current t ptr currentSize pc live fresh
      have effect := lane_effect (config positive) op l current t ptr currentSize
      have frame := (segmentReference_concrete (lane_regular (config positive) op l current t ptr currentSize)).frame
      change _ ∧ _ ∧ (finish (config positive) op t current).barrier=current.barrier at frame
      refine ⟨events++added,done (config positive) op t current,concrete_runs_append run localRun,?_⟩
      constructor
      · simpa [done,setLane,effect.1] using inv.length
      · simpa [done,setLane,effect.2.1] using inv.sharedEq
      · simpa [done,setLane,frame.2.2] using inv.barrier
      · intro u hu
        have ne : u≠t := by intro h; subst u; dsimp [t] at hu; omega
        simp only [done,setLane,Function.update_of_ne ne]
        rw [effect.2.2.2 u ne]
        exact inv.pending u (by omega)
      · intro u hu
        by_cases eq : u=t
        · subst u; simp [done,setLane]
        · have earlier : u.val<count := by have ne : u.val≠count := fun h => eq (Fin.ext h); omega
          simp only [done,setLane,Function.update_of_ne eq]
          rw [effect.2.2.2 u eq]
          exact inv.halted u earlier
  obtain ⟨events,final,run,inv⟩ := aux n (Nat.le_refl _)
  exact ⟨events,final,run,fun t => inv.halted t t.isLt⟩

/-- The concrete witness is admitted by the same memory model used by universal
correctness. Existence is established without numerical assumptions. -/
theorem admitted_exists (op : Op) (l : Layout n) (global shared : List Word) (seeds : Fin n → Scalar.State)
    (positive : 0<n) (size : l.prefixWords+n≤global.length) :
    ∃ events final, ∃ run : Runs (config positive) (program op) (initial l global shared seeds) events final,
      (∀ t, (final.lanes t).halted=true) ∧ ∃ source co, Admitted op l global shared seeds run source co := by
  obtain ⟨events,final,run,halted⟩ := execution_exists op l global shared seeds positive size
  obtain ⟨source,co,valid,_⟩ := Memory.Chronology.concrete_admitted run rfl
  exact ⟨events,final,run.toRuns,halted,source,co,valid⟩

end Ptx.Scalar.Parallel.Pointwise
