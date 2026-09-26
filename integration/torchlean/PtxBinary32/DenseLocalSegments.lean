import PtxBinary32.DenseOutput

/-! Straight-line dense segments separate the physical lane from the logical
matrix index. They retain the original fetched instruction lists and prove
concrete loads address allocated storage for any permitted input bit patterns. -/
namespace Ptx.Scalar.Parallel.Dense.Local
open Dense
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000

private theorem update_shadow (f : Nat → α) (i : Nat) (a b : α) :
    Scalar.update (Scalar.update f i a) i b=Scalar.update f i b := by
  funext j
  by_cases h : j=i <;> simp [Scalar.update,h]

def afterSetup (s : Shape) (cfg : Parallel.Config n) (state : Parallel.State n) (t : Fin n) (logical : Fin s.threads) : Parallel.State n :=
  let r := logical.val / s.width
  let c := logical.val % s.width
  let old := (state.lanes t).scalar
  let regs := Scalar.update (Scalar.update (Scalar.update (Scalar.update (Scalar.update old.regs
    1 (BitVec.ofNat 32 c)) 2 (BitVec.ofNat 32 r)) 3 (BitVec.ofNat 32 (r*s.columns+c+s.weightBase))) 4 0) 5 0
  setLane state t {state.lanes t with scalar := {old with pc := old.pc+8,regs := regs,preds := Scalar.update old.preds 0 (decide (c<s.columns)),memory := []}}

theorem setup_execution (s : Shape) (b : ArithmeticBounds s) (cfg : Parallel.Config n) (state : Parallel.State n) (t : Fin n) (logical : Fin s.threads)
    (tid : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 logical.val) :
    SegmentRegular cfg t ((products s).take 8) state ∧
    (segmentReference cfg t ((products s).take 8) state).1 = afterSetup s cfg state t logical := by
  have coords := decoded_coordinates s b logical
  have hc := congrArg (BitVec.ofNat 32) coords.1
  have hr := congrArg (BitVec.ofNat 32) coords.2
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at hc hr
  simp only [Scalar.BinOp.eval,BitVec.toNat_ofNat] at hc hr
  have df : s.depth < 4294967296 := by have := b.depth; omega
  have shift : (BitVec.ofNat 32 logical.val >>> s.depth) = BitVec.ofNat 32 (logical.val / s.width) := by
    simpa [Nat.mod_eq_of_lt df,b.depth] using hr
  have cf : logical.val % s.width < 4294967296 := by
    have := (coordinates s logical).2.1; have := width_fits s b; omega
  have nf : s.columns < 4294967296 := by
    have padded : s.columns ≤ s.width := s.padded; have := width_fits s b; omega
  simp [SegmentRegular,segmentReference,products,pointer,scalar,word,Reference.dispatch,scalarStep,
    Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
    Scalar.Operand64.eval,setLane,arena,tid,Scalar.update,Function.update,
    afterSetup,update_shadow,hc,shift,Nat.mod_eq_of_lt df,b.depth,Scalar.BinOp.eval,Scalar.Compare.eval,
    ← BitVec.ofNat_mul,← BitVec.ofNat_add,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt nf,
    Shape.weightBase,Nat.add_assoc]

def productFinish (s : Shape) (b : ArithmeticBounds s) (cfg : Parallel.Config n) (state : Parallel.State n) (t : Fin n) (logical : Fin s.threads) : Parallel.State n :=
  let column := logical.val % s.width
  let index := s.weight (logical.val / s.width) column
  let a := afterSetup s cfg state t logical
  let a := afterPointer a t 0 column
  let a := afterLoad a t .global 4 column
  let a := afterPointer a t 1 index
  let a := afterLoad a t .global 5 index
  let a := (Reference.dispatch cfg t (.binary32 ⟨.always,.mul,6,.reg 5,.reg 4⟩) a).state
  let a := afterPointer a t 2 logical.val
  (Reference.dispatch cfg t (.memory .shared (.plain (.store (.reg 2) (.reg 6)))) a).state

private theorem pointer_segment (cfg : Config n) (state : Parallel.State n) (t : Fin n)
    (destination source index : Nat)
    (operand : (state.lanes t).scalar.regs source = BitVec.ofNat 32 index) (fits : index < 2^32) :
    ∃ events, ConcreteSegment cfg t (pointer destination source) state events (afterPointer state t destination index) := by
  obtain ⟨regular,result⟩ := pointer_execution cfg state t destination source index operand fits
  exact ⟨_,result ▸ segmentReference_concrete regular⟩

private theorem load_segment (cfg : Config n) (state : Parallel.State n) (t : Fin n)
    (space : Space) (destination address index : Nat)
    (valid : (state.lanes t).scalar.preds 0 = true →
      Scalar.addressIndex (arena state (some space)) ((state.lanes t).scalar.addrs address) = .ok index) :
    ∃ events, ConcreteSegment cfg t [guarded space (.load destination (.reg address))] state events
      (afterLoad state t space destination index) := by
  obtain ⟨regular,result⟩ := guarded_load_execution cfg state t space destination address index valid
  exact ⟨_,result ▸ segmentReference_concrete regular⟩

/-- Every product lane, including a padded lane, has a complete instruction
segment. This is an actual-dispatch witness, not a supplied product value. -/
theorem product_segment (s : Shape) (b : ArithmeticBounds s) (cfg : Parallel.Config n) (state : Parallel.State n) (t : Fin n) (logical : Fin s.threads)
    (tid : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 logical.val)
    (global : s.globalWords ≤ state.global.length) (shared : s.sharedWords ≤ state.shared.length) :
    ∃ events, ConcreteSegment cfg t ((products s).take 21) state events (productFinish s b cfg state t logical) := by
  let c := logical.val % s.width
  let r := logical.val / s.width
  let index := s.weight r c
  have cf : c < 2^32 := lt_trans (coordinates s logical).2.1 (width_fits s b)
  have wf : index < 2^32 := weight_index_fits s b logical
  have tf := thread_fits s b logical
  have cp : 4*c < 2^64 := by omega
  have wp : 4*index < 2^64 := by omega
  have tp : 4*logical.val < 2^64 := by omega
  let a := afterSetup s cfg state t logical
  let d := afterPointer a t 0 c
  let e := afterLoad d t .global 4 c
  let f := afterPointer e t 1 index
  let g := afterLoad f t .global 5 index
  let h := (Reference.dispatch cfg t (.binary32 ⟨.always,.mul,6,.reg 5,.reg 4⟩) g).state
  let j := afterPointer h t 2 logical.val
  obtain ⟨setupOK,setupValue⟩ := setup_execution s b cfg state t logical tid
  have setupRun := segmentReference_concrete setupOK
  rw [setupValue] at setupRun
  obtain ⟨ev0,ptr0⟩ := pointer_segment cfg a t 0 1 c
    (by simp [a,afterSetup,setLane,ite_apply,Scalar.update,c]) cf
  obtain ⟨ev1,ld0⟩ := load_segment cfg d t .global 4 0 c (by
    intro active
    have hc : c < s.columns := by simpa [d,a,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,c] using active
    have extent : c < state.global.length := by
      simp only [Shape.globalWords,Shape.outputBase,Shape.biasBase] at global
      omega
    simpa [d,a,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,arena] using pointer_index state.global c extent cp)
  obtain ⟨ev2,ptr1⟩ := pointer_segment cfg e t 1 3 index
    (by simp [e,d,a,afterLoad,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,index,r,c,Shape.weight,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]) wf
  obtain ⟨ev3,ld1⟩ := load_segment cfg f t .global 5 1 index (by
    intro active
    have hc : c < s.columns := by simpa [f,e,d,a,afterLoad,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,c] using active
    have wi := (weight_bound s r c (coordinates s logical).1 hc).2
    have extent : index < state.global.length := by
      simp only [Shape.globalWords,Shape.outputBase] at global
      dsimp [index]; omega
    simpa [f,e,d,a,afterLoad,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,arena] using pointer_index state.global index extent wp)
  have mulRun := segmentReference_concrete (binary32_regular cfg g t ⟨.always,.mul,6,.reg 5,.reg 4⟩)
  obtain ⟨ev4,ptr2⟩ := pointer_segment cfg h t 2 0 logical.val (by
    simp [h,g,f,e,d,a,Reference.dispatch,Reference.binary32,Scalar.Guard.eval,afterLoad,afterPointer,afterSetup,setLane,ite_apply,Scalar.update,tid]) tf
  have si : logical.val < state.shared.length := by
    have ht := logical.isLt
    have mono : s.threads ≤ s.sharedWords := by
      change s.threads ≤ (s.depth+1)*s.threads
      nlinarith
    omega
  have address : Scalar.addressIndex j.shared ((j.lanes t).scalar.addrs 2) = .ok logical.val := by
    simpa [j,h,g,f,e,d,a,afterPointer,afterLoad,afterSetup,setLane,ite_apply,Scalar.update,Reference.dispatch,
      Reference.binary32,Scalar.Guard.eval] using pointer_index state.shared logical.val si tp
  have storeOK : SegmentRegular cfg t [.memory .shared (.plain (.store (.reg 2) (.reg 6)))] j := by
    simp [SegmentRegular,Reference.dispatch,scalarStep,Scalar.eval,Scalar.Instr.plain,
      Scalar.Guard.eval,Scalar.Operand64.eval,setLane,arena,address]
  have storeRun := segmentReference_concrete storeOK
  have all := ((((((setupRun.append ptr0).append ld0).append ptr1).append ld1).append mulRun).append ptr2).append storeRun
  exact ⟨_,all⟩

theorem round_regular (s : Shape) (b : ArithmeticBounds s) (k : Nat) (hk : k < s.depth)
    (cfg : Parallel.Config n) (state : Parallel.State n) (t : Fin n) (logical : Fin s.threads)
    (tid : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 logical.val)
    (column : (state.lanes t).scalar.regs 1 = BitVec.ofNat 32 (logical.val%s.width))
    (shared : s.sharedWords ≤ state.shared.length) :
    SegmentRegular cfg t ((round s k).take 15) state := by
  have indices := round_indices s b k hk logical
  have aFit : leftIndex s k logical < 4294967296 := indices.1
  have bFit : nextIndex s k logical < 4294967296 := by have := b.arithmetic; omega
  have cf : logical.val%s.width < 4294967296 := lt_trans (coordinates s logical).2.1 (width_fits s b)
  have af : 2^(s.depth-(k+1)) < 4294967296 := by
    have : 2^(s.depth-(k+1)) ≤ s.width := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have := width_fits s b; omega
  have ai : 4*(leftIndex s k logical) < 18446744073709551616 := by omega
  have ar : 4*(leftIndex s k logical+1) < 18446744073709551616 := by omega
  have bi : 4*(nextIndex s k logical) < 18446744073709551616 := by omega
  have nb : nextIndex s k logical < state.shared.length := by omega
  have four : ∀ x : Nat, (x+x)+(x+x) = 4*x := by intro x; omega
  have succFour : ∀ x : Nat, 4*x+4 = 4*(x+1) := by intro x; omega
  dsimp [leftIndex,nextIndex] at aFit bFit ai ar bi nb
  by_cases active : logical.val%s.width < 2^(s.depth-(k+1))
  · have right : leftIndex s k logical+1 < state.shared.length := by have := indices.2.2 active; omega
    have left : leftIndex s k logical < state.shared.length := by omega
    dsimp [leftIndex] at right left
    simp [SegmentRegular,round,pointer,scalar,guarded,word,Reference.dispatch,Reference.binary32,
      scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
      Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,setLane,arena,Scalar.update,
      tid,column,← BitVec.ofNat_add,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt af,active,
      four,succFour,
      Nat.mod_eq_of_lt aFit,Nat.mod_eq_of_lt bFit,Scalar.addressIndex,
      Nat.mod_eq_of_lt ai,Nat.mod_eq_of_lt ar,Nat.mod_eq_of_lt bi,left,right,nb] 
  · simp [SegmentRegular,round,pointer,scalar,guarded,word,Reference.dispatch,Reference.binary32,
      scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
      Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,setLane,arena,Scalar.update,
      tid,column,← BitVec.ofNat_add,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt af,active]

theorem output_regular (s : Shape) (b : ArithmeticBounds s) (cfg : Parallel.Config n) (state : Parallel.State n) (t : Fin n) (logical : Fin s.threads)
    (regs : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 logical.val ∧
      (state.lanes t).scalar.regs 1 = BitVec.ofNat 32 (logical.val%s.width) ∧
      (state.lanes t).scalar.regs 2 = BitVec.ofNat 32 (logical.val/s.width))
    (global : s.globalWords ≤ state.global.length) (shared : s.sharedWords ≤ state.shared.length) :
    SegmentRegular cfg t ((output s).take 19) state := by
  have bounds := output_indices s logical
  have large := b.arithmetic
  have rf : rootIndex s logical < 4294967296 := by omega
  have bf : biasIndex s logical < 4294967296 := by
    have : s.outputBase ≤ s.globalWords := by dsimp [Shape.globalWords]; omega
    omega
  have ofit : outputIndex s logical < 4294967296 := by omega
  have cf : logical.val%s.width < 4294967296 := lt_trans (coordinates s logical).2.1 (width_fits s b)
  have rp : 4*rootIndex s logical < 18446744073709551616 := by omega
  have bp : 4*biasIndex s logical < 18446744073709551616 := by omega
  have op : 4*outputIndex s logical < 18446744073709551616 := by omega
  have rb : rootIndex s logical < state.shared.length := by omega
  have bb : biasIndex s logical < state.global.length := by
    have : s.outputBase ≤ s.globalWords := by dsimp [Shape.globalWords]; omega
    omega
  have ob : outputIndex s logical < state.global.length := by omega
  have four : ∀ x : Nat, (x+x)+(x+x)=4*x := by intro x; omega
  dsimp [rootIndex,biasIndex,outputIndex] at rf bf ofit rp bp op rb bb ob
  have gate : (BitVec.ofNat 32 (logical.val%s.width) == (BitVec.ofNat 32 0)) = decide (logical.val%s.width=0) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf]
  have iszero : BitVec.ofNat 32 (logical.val%s.width) = (BitVec.ofNat 32 0) ↔ logical.val%s.width=0 := by
    simp [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf]
  by_cases leader : logical.val%s.width=0
  all_goals cases mode : s.relu
  all_goals by_cases neg : 2147483648 ≤ (Ptx.Binary32.reference .add state.shared[rootIndex s logical]! state.global[biasIndex s logical]!).toNat
  all_goals by_cases oldneg : 2147483648 ≤ ((state.lanes t).scalar.regs 6).toNat
  all_goals dsimp [rootIndex,biasIndex] at neg
  all_goals simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem rb,List.getElem?_eq_getElem bb,Option.getD_some] at neg
  all_goals
    simp [mode,SegmentRegular,output,pointer,scalar,guarded,word,Reference.dispatch,Reference.binary32,
      scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
      Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,setLane,arena,Scalar.update,
      regs.1,regs.2.1,regs.2.2,gate,iszero,neg,oldneg,rootIndex,biasIndex,← BitVec.ofNat_add,Nat.mod_eq_of_lt cf,leader,four,
      Nat.mod_eq_of_lt rf,Nat.mod_eq_of_lt bf,Nat.mod_eq_of_lt ofit,Scalar.addressIndex,
      Nat.mod_eq_of_lt rp,Nat.mod_eq_of_lt bp,Nat.mod_eq_of_lt op,rb,bb,ob]



end Ptx.Scalar.Parallel.Dense.Local
