import PtxBinary32.DenseSegments
import PtxBinary32.DenseArithmetic

namespace Ptx.Scalar.Parallel.Dense
set_option maxRecDepth 6000
set_option maxHeartbeats 1500000

/-- Register addresses are computed even for padding, but padded loads are
predicated off. Their intermediate index still fits the chosen word arithmetic. -/
theorem weight_index_fits (s : Shape) (b : Bounds s) (t : Fin s.threads) :
    s.weight (t.val / s.width) (t.val % s.width) < 2^32 := by
  obtain ⟨hr,hc,_⟩ := coordinates s t
  have hmul := Nat.mul_le_mul_right s.columns hr
  simp only [Nat.succ_mul] at hmul
  have large := b.arithmetic
  simp only [Shape.globalWords,Shape.outputBase,Shape.biasBase] at large
  simp only [Shape.weight,Shape.weightBase]
  omega

def productFinish (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads) : Parallel.State s.threads :=
  let column := t.val % s.width
  let index := s.weight (t.val / s.width) column
  let a := afterSetup s state t
  let a := afterPointer a t 0 column
  let a := afterLoad a t .global 4 column
  let a := afterPointer a t 1 index
  let a := afterLoad a t .global 5 index
  let a := (Reference.dispatch (config s b) t (.binary32 ⟨.always,.mul,6,.reg 5,.reg 4⟩) a).state
  let a := afterPointer a t 2 t.val
  (Reference.dispatch (config s b) t (.memory .shared (.plain (.store (.reg 2) (.reg 6)))) a).state

private theorem pointer_segment (cfg : Config n) (state : Parallel.State n) (t : Fin n)
    (destination source index : Nat)
    (operand : (state.lanes t).scalar.regs source = BitVec.ofNat 32 index) (fits : index < 2^32) :
    ∃ events, Segment cfg t (pointer destination source) state events (afterPointer state t destination index) := by
  obtain ⟨regular,result⟩ := pointer_execution cfg state t destination source index operand fits
  exact ⟨_,result ▸ segmentReference_sound regular⟩

private theorem load_segment (cfg : Config n) (state : Parallel.State n) (t : Fin n)
    (space : Space) (destination address index : Nat)
    (valid : (state.lanes t).scalar.preds 0 = true →
      Scalar.addressIndex (arena state (some space)) ((state.lanes t).scalar.addrs address) = .ok index) :
    ∃ events, Segment cfg t [guarded space (.load destination (.reg address))] state events
      (afterLoad state t space destination index) := by
  obtain ⟨regular,result⟩ := guarded_load_execution cfg state t space destination address index valid
  exact ⟨_,result ▸ segmentReference_sound regular⟩

/-- Every product lane, including a padded lane, has a complete instruction
segment. This is an actual-dispatch witness, not a supplied product value. -/
theorem product_segment (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads)
    (tid : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val)
    (global : s.globalWords ≤ state.global.length) (shared : s.sharedWords ≤ state.shared.length) :
    ∃ events, Segment (config s b) t ((products s).take 21) state events (productFinish s b state t) := by
  let c := t.val % s.width
  let r := t.val / s.width
  let index := s.weight r c
  have cf : c < 2^32 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have wf : index < 2^32 := weight_index_fits s b t
  have tf := thread_fits s b t
  have cp : 4*c < 2^64 := by omega
  have wp : 4*index < 2^64 := by omega
  have tp : 4*t.val < 2^64 := by omega
  let a := afterSetup s state t
  let d := afterPointer a t 0 c
  let e := afterLoad d t .global 4 c
  let f := afterPointer e t 1 index
  let g := afterLoad f t .global 5 index
  let h := (Reference.dispatch (config s b) t (.binary32 ⟨.always,.mul,6,.reg 5,.reg 4⟩) g).state
  let j := afterPointer h t 2 t.val
  obtain ⟨setupOK,setupValue⟩ := setup_execution s b state t tid
  have setupRun := segmentReference_sound setupOK
  rw [setupValue] at setupRun
  obtain ⟨ev0,ptr0⟩ := pointer_segment (config s b) a t 0 1 c
    (by simp [a,afterSetup,setLane,ite_apply,Scalar.update,c]) cf
  obtain ⟨ev1,ld0⟩ := load_segment (config s b) d t .global 4 0 c (by
    intro active
    have hc : c < s.columns := by simpa [d,a,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,c] using active
    have extent : c < state.global.length := by
      simp only [Shape.globalWords,Shape.outputBase,Shape.biasBase] at global
      omega
    simpa [d,a,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,arena] using pointer_index state.global c extent cp)
  obtain ⟨ev2,ptr1⟩ := pointer_segment (config s b) e t 1 3 index
    (by simp [e,d,a,afterLoad,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,index,r,c,Shape.weight,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]) wf
  obtain ⟨ev3,ld1⟩ := load_segment (config s b) f t .global 5 1 index (by
    intro active
    have hc : c < s.columns := by simpa [f,e,d,a,afterLoad,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,c] using active
    have wi := (weight_bound s r c (coordinates s t).1 hc).2
    have extent : index < state.global.length := by
      simp only [Shape.globalWords,Shape.outputBase] at global
      dsimp [index]; omega
    simpa [f,e,d,a,afterLoad,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,arena] using pointer_index state.global index extent wp)
  have mulRun := segmentReference_sound (binary32_regular (config s b) g t ⟨.always,.mul,6,.reg 5,.reg 4⟩)
  obtain ⟨ev4,ptr2⟩ := pointer_segment (config s b) h t 2 0 t.val (by
    simp [h,g,f,e,d,a,Reference.dispatch,Reference.binary32,Scalar.Guard.eval,afterLoad,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,tid]) tf
  have si : t.val < state.shared.length := by
    have ht := t.isLt
    have mono : s.threads ≤ s.sharedWords := by
      change s.threads ≤ (s.depth+1)*s.threads
      nlinarith
    omega
  have address : Scalar.addressIndex j.shared ((j.lanes t).scalar.addrs 2) = .ok t.val := by
    simpa [j,h,g,f,e,d,a,afterPointer,afterLoad,afterSetup,setLane,ite_apply,Scalar.update,Reference.dispatch,
      Reference.binary32,Scalar.Guard.eval] using pointer_index state.shared t.val si tp
  have storeOK : SegmentRegular (config s b) t [.memory .shared (.plain (.store (.reg 2) (.reg 6)))] j := by
    simp [SegmentRegular,Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,
      Scalar.Guard.eval,Scalar.Operand64.eval,setLane,arena,address]
  have storeRun := segmentReference_sound storeOK
  have all := ((((((setupRun.append ptr0).append ld0).append ptr1).append ld1).append mulRun).append ptr2).append storeRun
  exact ⟨_,all⟩

theorem products_fetch (s : Shape) : Fetches (program s) 0 ((products s).take 21) := by
  intro k hk
  have bound : k < 21 := by simpa using hk
  have inside : k < (products s).length := by rw [products_length]; omega
  have h22 : k < 22 := by omega
  simp [program,List.getElem?_append,inside,List.getElem?_take,bound,h22]

theorem product_run (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads)
    (tid : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val)
    (pc : (state.lanes t).scalar.pc = 0) (live : (state.lanes t).halted = false)
    (fresh : state.barrier.arrived t = false)
    (global : s.globalWords ≤ state.global.length) (shared : s.sharedWords ≤ state.shared.length) :
    ∃ events, Runs (config s b) (program s) state events (productFinish s b state t) := by
  obtain ⟨events,segment⟩ := product_segment s b state t tid global shared
  exact ⟨events,segment.compile (by rw [pc]; exact products_fetch s) live fresh (by change 94 = 94 ∧ 70 ≤ 70; decide)⟩

theorem product_memory (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads)
    (shared : s.sharedWords ≤ state.shared.length) :
    (productFinish s b state t).global = state.global ∧
    (productFinish s b state t).shared = state.shared.set t.val
      (nodeValue s state.global (t.val/s.width) 0 (t.val%s.width)) := by
  have ti := t.isLt
  have mono : s.threads ≤ s.sharedWords := by
    change s.threads ≤ (s.depth+1)*s.threads
    nlinarith
  have inside : t.val < state.shared.length := by omega
  have tf := thread_fits s b t
  have address := pointer_index state.shared t.val inside (by omega)
  by_cases active : t.val%s.width < s.columns
  all_goals simp [productFinish,afterSetup,afterLoad,afterPointer,Reference.dispatch,
    Reference.binary32,Scalar.Guard.eval,setLane,Scalar.update,ite_apply,Scalar.Operand32.eval,
    scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Operand64.eval,arena,address,
    operands,nodeValue,active,Shape.weight,Shape.weightBase,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- The product instructions touch only their own lane and preserve the barrier
resource and site. This is proved from the executable poststate, not assumed as
part of the segment interface. -/
theorem product_control (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads)
    (shared : s.sharedWords ≤ state.shared.length) :
    (productFinish s b state t).barrier = state.barrier ∧
    (productFinish s b state t).site = state.site ∧
    ((productFinish s b state t).lanes t).scalar.regs 0 = (state.lanes t).scalar.regs 0 ∧
    (∀ u, u ≠ t → (productFinish s b state t).lanes u = state.lanes u) := by
  have ti := t.isLt
  have mono : s.threads ≤ s.sharedWords := by
    change s.threads ≤ (s.depth+1)*s.threads
    nlinarith
  have inside : t.val < state.shared.length := by omega
  have tf := thread_fits s b t
  have address := pointer_index state.shared t.val inside (by omega)
  simp [productFinish,afterSetup,afterLoad,afterPointer,Reference.dispatch,
    Reference.binary32,Scalar.Guard.eval,setLane,Scalar.update,ite_apply,Scalar.Operand32.eval,
    scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Operand64.eval,arena,address]
  intro u ne
  simp [Function.update,ne,Ne.symm ne]

theorem product_coordinates (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads)
    (shared : s.sharedWords ≤ state.shared.length) :
    ((productFinish s b state t).lanes t).scalar.regs 1 = BitVec.ofNat 32 (t.val%s.width) ∧
    ((productFinish s b state t).lanes t).scalar.regs 2 = BitVec.ofNat 32 (t.val/s.width) := by
  have ti := t.isLt
  have mono : s.threads ≤ s.sharedWords := by
    change s.threads ≤ (s.depth+1)*s.threads
    nlinarith
  have inside : t.val < state.shared.length := by omega
  have tf := thread_fits s b t
  have address := pointer_index state.shared t.val inside (by omega)
  simp [productFinish,afterSetup,afterLoad,afterPointer,Reference.dispatch,
    Reference.binary32,Scalar.Guard.eval,setLane,Scalar.update,ite_apply,Scalar.Operand32.eval,
    scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Operand64.eval,arena,address]

end Ptx.Scalar.Parallel.Dense
