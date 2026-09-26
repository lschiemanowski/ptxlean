import PtxBinary32.DenseRoundPhase

namespace Ptx.Scalar.Parallel.Dense
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000

def rootIndex (s : Shape) (t : Fin s.threads) := t.val+s.depth*s.threads
def biasIndex (s : Shape) (t : Fin s.threads) := t.val/s.width+s.biasBase
def outputIndex (s : Shape) (t : Fin s.threads) := t.val/s.width+s.outputBase

theorem output_indices (s : Shape) (t : Fin s.threads) :
    rootIndex s t < s.sharedWords ∧ biasIndex s t < s.outputBase ∧
    s.outputBase ≤ outputIndex s t ∧ outputIndex s t < s.globalWords := by
  have ti := t.isLt
  have row := (coordinates s t).1
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [rootIndex,Shape.sharedWords]; rw [Nat.add_mul,Nat.one_mul]; omega
  · dsimp [biasIndex,Shape.outputBase]; omega
  · exact Nat.le_add_left _ _
  · dsimp [outputIndex,Shape.globalWords]; omega

def outputFinish (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads) :=
  (segmentReference (config s b) t ((output s).take 19) state).1

def outputValue (s : Shape) (state : Parallel.State s.threads) (t : Fin s.threads) : Word :=
  activate s (Ptx.Binary32.reference .add state.shared[rootIndex s t]! state.global[biasIndex s t]!)

theorem output_regular (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads)
    (regs : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val ∧
      (state.lanes t).scalar.regs 1 = BitVec.ofNat 32 (t.val%s.width) ∧
      (state.lanes t).scalar.regs 2 = BitVec.ofNat 32 (t.val/s.width))
    (global : s.globalWords ≤ state.global.length) (shared : s.sharedWords ≤ state.shared.length) :
    SegmentRegular (config s b) t ((output s).take 19) state := by
  have bounds := output_indices s t
  have large := b.arithmetic
  have rf : rootIndex s t < 4294967296 := by omega
  have bf : biasIndex s t < 4294967296 := by
    have : s.outputBase ≤ s.globalWords := by dsimp [Shape.globalWords]; omega
    omega
  have ofit : outputIndex s t < 4294967296 := by omega
  have cf : t.val%s.width < 4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have rp : 4*rootIndex s t < 18446744073709551616 := by omega
  have bp : 4*biasIndex s t < 18446744073709551616 := by omega
  have op : 4*outputIndex s t < 18446744073709551616 := by omega
  have rb : rootIndex s t < state.shared.length := by omega
  have bb : biasIndex s t < state.global.length := by
    have : s.outputBase ≤ s.globalWords := by dsimp [Shape.globalWords]; omega
    omega
  have ob : outputIndex s t < state.global.length := by omega
  have four : ∀ x : Nat, (x+x)+(x+x)=4*x := by intro x; omega
  dsimp [rootIndex,biasIndex,outputIndex] at rf bf ofit rp bp op rb bb ob
  have gate : (BitVec.ofNat 32 (t.val%s.width) == (BitVec.ofNat 32 0)) = decide (t.val%s.width=0) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf]
  have iszero : BitVec.ofNat 32 (t.val%s.width) = (BitVec.ofNat 32 0) ↔ t.val%s.width=0 := by
    simp [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf]
  by_cases leader : t.val%s.width=0
  all_goals cases mode : s.relu
  all_goals by_cases neg : 2147483648 ≤ (Ptx.Binary32.reference .add state.shared[rootIndex s t]! state.global[biasIndex s t]!).toNat
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


theorem output_effect (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads)
    (regs : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val ∧
      (state.lanes t).scalar.regs 1 = BitVec.ofNat 32 (t.val%s.width) ∧
      (state.lanes t).scalar.regs 2 = BitVec.ofNat 32 (t.val/s.width))
    (global : s.globalWords ≤ state.global.length) (shared : s.sharedWords ≤ state.shared.length) :
    (outputFinish s b state t).global =
      (if t.val%s.width=0 then state.global.set (outputIndex s t) (outputValue s state t) else state.global) ∧
    (outputFinish s b state t).shared = state.shared ∧
    (outputFinish s b state t).site = state.site ∧
    (∀ u, u≠t → (outputFinish s b state t).lanes u = state.lanes u) := by
  have bounds := output_indices s t
  have large := b.arithmetic
  have rf : rootIndex s t < 4294967296 := by omega
  have bf : biasIndex s t < 4294967296 := by
    have : s.outputBase ≤ s.globalWords := by dsimp [Shape.globalWords]; omega
    omega
  have ofit : outputIndex s t < 4294967296 := by omega
  have cf : t.val%s.width < 4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have rp : 4*rootIndex s t < 18446744073709551616 := by omega
  have bp : 4*biasIndex s t < 18446744073709551616 := by omega
  have op : 4*outputIndex s t < 18446744073709551616 := by omega
  have rb : rootIndex s t < state.shared.length := by omega
  have bb : biasIndex s t < state.global.length := by
    have : s.outputBase ≤ s.globalWords := by dsimp [Shape.globalWords]; omega
    omega
  have ob : outputIndex s t < state.global.length := by omega
  have four : ∀ x : Nat, (x+x)+(x+x)=4*x := by intro x; omega
  dsimp [rootIndex,biasIndex,outputIndex] at rf bf ofit rp bp op rb bb ob
  have gate : (BitVec.ofNat 32 (t.val%s.width) == (BitVec.ofNat 32 0)) = decide (t.val%s.width=0) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf]
  have iszero : BitVec.ofNat 32 (t.val%s.width) = (BitVec.ofNat 32 0) ↔ t.val%s.width=0 := by
    simp [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf]
  by_cases leader : t.val%s.width=0
  all_goals cases mode : s.relu
  all_goals by_cases neg : 2147483648 ≤ (Ptx.Binary32.reference .add state.shared[rootIndex s t]! state.global[biasIndex s t]!).toNat
  all_goals by_cases oldneg : 2147483648 ≤ ((state.lanes t).scalar.regs 6).toNat
  all_goals dsimp [rootIndex,biasIndex] at neg
  all_goals simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem rb,List.getElem?_eq_getElem bb,Option.getD_some] at neg
  all_goals
    simp [mode,activate,outputFinish,segmentReference,outputValue,← relu_bits,outputIndex,output,pointer,scalar,guarded,word,Reference.dispatch,Reference.binary32,
      scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
      Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,setLane,arena,Scalar.update,
      regs.1,regs.2.1,regs.2.2,gate,iszero,neg,oldneg,rootIndex,biasIndex,← BitVec.ofNat_add,Nat.mod_eq_of_lt cf,leader,four,
      Nat.mod_eq_of_lt rf,Nat.mod_eq_of_lt bf,Nat.mod_eq_of_lt ofit,Scalar.addressIndex,
      Nat.mod_eq_of_lt rp,Nat.mod_eq_of_lt bp,Nat.mod_eq_of_lt op,rb,bb,ob]


  all_goals intro u ne; simp [Function.update,ne]

def outputDone (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads) :=
  let last := outputFinish s b state t
  setLane last t {last.lanes t with halted := true}

theorem output_fetch (s : Shape) : Fetches (program s) (22+16*s.depth) (output s) := by
  have fetch := fetches_slice (products s ++ (List.range s.depth).flatMap (round s)) (output s) []
  simpa [program,List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch

theorem output_run (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads)
    (regs : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val ∧
      (state.lanes t).scalar.regs 1 = BitVec.ofNat 32 (t.val%s.width) ∧
      (state.lanes t).scalar.regs 2 = BitVec.ofNat 32 (t.val/s.width))
    (global : s.globalWords ≤ state.global.length) (shared : s.sharedWords ≤ state.shared.length)
    (pc : (state.lanes t).scalar.pc = 22+16*s.depth)
    (live : (state.lanes t).halted = false) (fresh : state.barrier.arrived t = false) :
    ∃ events, ConcreteRuns (config s b) (program s) state events (outputDone s b state t) := by
  have segment := segmentReference_concrete (output_regular s b state t regs global shared)
  have frame := segment.frame
  change ((outputFinish s b state t).lanes t).scalar.pc = (state.lanes t).scalar.pc + ((output s).take 19).length ∧
    ((outputFinish s b state t).lanes t).halted = (state.lanes t).halted ∧
    (outputFinish s b state t).barrier = state.barrier at frame
  have eligible : Mixed.Eligible (config s b).target := by change 94=94 ∧ 70≤70; decide
  have run := segment.compile (program := program s) (by
    rw [pc]; intro j hj
    have bound : j<19 := by simpa using hj
    rw [output_fetch s j (by simp; omega)]
    simp [bound]) live fresh eligible
  have lastpc : ((outputFinish s b state t).lanes t).scalar.pc = 22+16*s.depth+19 := by
    simpa [pc] using frame.1
  have fetch : (program s)[22+16*s.depth+19]? = some .exit := by
    rw [output_fetch s 19 (by simp)]; exact output_exit s
  have step : Step (config s b) (program s) none t (outputFinish s b state t)
      (Reference.dispatch (config s b) t .exit (outputFinish s b state t)) := by
    refine ⟨eligible,?_⟩
    change (if ((outputFinish s b state t).lanes t).halted then _ else _) 
    have hl : ((outputFinish s b state t).lanes t).halted = false := frame.2.1.trans live
    have hf : (outputFinish s b state t).barrier.arrived t = false := by rw [frame.2.2]; exact fresh
    simp only [hl,hf,Bool.false_eq_true,ite_false,lastpc,fetch]
    exact Dispatch.exit
  have one := ConcreteRuns.cons step (ConcreteRuns.nil (s := outputDone s b state t))
  exact ⟨_,concrete_runs_append run one⟩

end Ptx.Scalar.Parallel.Dense
