import PtxBinary32.DenseProducts

/-! The actual shared-memory reduction segment, including inactive lanes.
Each round writes a fresh plane. Selected array reads are execution witnesses;
this module does not assume or claim memory-model admission. -/
namespace Ptx.Scalar.Parallel.Dense
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

def leftIndex (s : Shape) (k : Nat) (t : Fin s.threads) : Nat := t.val+t.val%s.width+k*s.threads
def nextIndex (s : Shape) (k : Nat) (t : Fin s.threads) : Nat := t.val+(k+1)*s.threads

theorem round_indices (s : Shape) (b : Bounds s) (k : Nat) (hk : k < s.depth) (t : Fin s.threads) :
    leftIndex s k t < 2^32 ∧ nextIndex s k t < s.sharedWords ∧
    (t.val%s.width < 2^(s.depth-(k+1)) → leftIndex s k t+1 < s.sharedWords) := by
  obtain ⟨hr,hc,ht⟩ := coordinates s t
  have kp : k*s.threads ≤ s.depth*s.threads := Nat.mul_le_mul_right _ (by omega)
  have np : (k+1)*s.threads ≤ s.depth*s.threads := Nat.mul_le_mul_right _ hk
  have ti := t.isLt
  have large := b.arithmetic
  have plane : s.sharedWords = s.depth*s.threads+s.threads := by simp [Shape.sharedWords,Nat.add_mul]
  refine ⟨?_,?_,?_⟩
  · dsimp [leftIndex]; omega
  · dsimp [nextIndex]; omega
  · intro active
    have child := (children_bound s k (t.val%s.width) hk active).2
    have width : 2^(s.depth-k) ≤ s.width := by
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have bound := scratch_bound s k (t.val/s.width) (2*(t.val%s.width)+1) (by omega) hr (by omega)
    simp only [Shape.scratch,Shape.thread] at bound ht
    dsimp [leftIndex]
    omega

theorem round_regular (s : Shape) (b : Bounds s) (k : Nat) (hk : k < s.depth)
    (state : Parallel.State s.threads) (t : Fin s.threads)
    (tid : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val)
    (column : (state.lanes t).scalar.regs 1 = BitVec.ofNat 32 (t.val%s.width))
    (shared : s.sharedWords ≤ state.shared.length) :
    SegmentRegular (config s b) t ((round s k).take 15) state := by
  have indices := round_indices s b k hk t
  have aFit : leftIndex s k t < 4294967296 := indices.1
  have bFit : nextIndex s k t < 4294967296 := by have := b.arithmetic; omega
  have cf : t.val%s.width < 4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have af : 2^(s.depth-(k+1)) < 4294967296 := by
    have : 2^(s.depth-(k+1)) ≤ s.width := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have := width_fits s b; omega
  have ai : 4*(leftIndex s k t) < 18446744073709551616 := by omega
  have ar : 4*(leftIndex s k t+1) < 18446744073709551616 := by omega
  have bi : 4*(nextIndex s k t) < 18446744073709551616 := by omega
  have nb : nextIndex s k t < state.shared.length := by omega
  have four : ∀ x : Nat, (x+x)+(x+x) = 4*x := by intro x; omega
  have succFour : ∀ x : Nat, 4*x+4 = 4*(x+1) := by intro x; omega
  dsimp [leftIndex,nextIndex] at aFit bFit ai ar bi nb
  by_cases active : t.val%s.width < 2^(s.depth-(k+1))
  · have right : leftIndex s k t+1 < state.shared.length := by have := indices.2.2 active; omega
    have left : leftIndex s k t < state.shared.length := by omega
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

def roundFinish (s : Shape) (b : Bounds s) (k : Nat) (state : Parallel.State s.threads) (t : Fin s.threads) :
    Parallel.State s.threads := (segmentReference (config s b) t ((round s k).take 15) state).1

theorem round_effect (s : Shape) (b : Bounds s) (k : Nat) (hk : k < s.depth)
    (state : Parallel.State s.threads) (t : Fin s.threads)
    (tid : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val)
    (column : (state.lanes t).scalar.regs 1 = BitVec.ofNat 32 (t.val%s.width))
    (shared : s.sharedWords ≤ state.shared.length) :
    (roundFinish s b k state t).global = state.global ∧
    (roundFinish s b k state t).shared =
      (if t.val%s.width < 2^(s.depth-(k+1)) then
        state.shared.set (nextIndex s k t)
          (Ptx.Binary32.reference .add state.shared[leftIndex s k t]! state.shared[leftIndex s k t+1]!)
       else state.shared) ∧
    (roundFinish s b k state t).site = state.site ∧
    ((roundFinish s b k state t).lanes t).scalar.regs 0 = (state.lanes t).scalar.regs 0 ∧
    ((roundFinish s b k state t).lanes t).scalar.regs 1 = (state.lanes t).scalar.regs 1 ∧
    ((roundFinish s b k state t).lanes t).scalar.regs 2 = (state.lanes t).scalar.regs 2 ∧
    (∀ u, u ≠ t → (roundFinish s b k state t).lanes u = state.lanes u) := by
  have indices := round_indices s b k hk t
  have aFit : leftIndex s k t < 4294967296 := indices.1
  have bFit : nextIndex s k t < 4294967296 := by have := b.arithmetic; omega
  have cf : t.val%s.width < 4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have af : 2^(s.depth-(k+1)) < 4294967296 := by
    have : 2^(s.depth-(k+1)) ≤ s.width := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have := width_fits s b; omega
  have ai : 4*(leftIndex s k t) < 18446744073709551616 := by omega
  have ar : 4*(leftIndex s k t+1) < 18446744073709551616 := by omega
  have bi : 4*(nextIndex s k t) < 18446744073709551616 := by omega
  have nb : nextIndex s k t < state.shared.length := by omega
  have four : ∀ x : Nat, (x+x)+(x+x) = 4*x := by intro x; omega
  have succFour : ∀ x : Nat, 4*x+4 = 4*(x+1) := by intro x; omega
  dsimp [leftIndex,nextIndex] at aFit bFit ai ar bi nb
  by_cases active : t.val%s.width < 2^(s.depth-(k+1))
  · have right : leftIndex s k t+1 < state.shared.length := by have := indices.2.2 active; omega
    have left : leftIndex s k t < state.shared.length := by omega
    dsimp [leftIndex] at right left
    simp [roundFinish,segmentReference,round,pointer,scalar,guarded,word,Reference.dispatch,Reference.binary32,
      scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
      Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,setLane,arena,Scalar.update,leftIndex,nextIndex,
      tid,column,← BitVec.ofNat_add,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt af,active,
      four,succFour,
      Nat.mod_eq_of_lt aFit,Nat.mod_eq_of_lt bFit,Scalar.addressIndex,
      Nat.mod_eq_of_lt ai,Nat.mod_eq_of_lt ar,Nat.mod_eq_of_lt bi,left,right,nb] 
    intro u ne
    simp [Function.update,ne]
  · simp [roundFinish,segmentReference,round,pointer,scalar,guarded,word,Reference.dispatch,Reference.binary32,
      scalarStep,Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
      Scalar.Operand64.eval,Scalar.BinOp.eval,Scalar.Compare.eval,setLane,arena,Scalar.update,leftIndex,nextIndex,
      tid,column,← BitVec.ofNat_add,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt af,active]

    intro u ne
    simp [Function.update,ne]

theorem program_round_split (s : Shape) (k : Nat) (hk : k < s.depth) :
    program s = (products s ++ (List.range k).flatMap (round s)) ++ round s k ++
      ((List.range' (k+1) (s.depth-(k+1))).flatMap (round s) ++ output s) := by
  have cut := List.range'_append_1 (s := 0) (m := k) (n := s.depth-k)
  simp only [Nat.zero_add,show k+(s.depth-k)=s.depth by omega] at cut
  have parts : List.range s.depth = List.range k ++ k :: List.range' (k+1) (s.depth-(k+1)) := by
    rw [List.range_eq_range',← cut]
    simp [List.range_eq_range',show s.depth-k=(s.depth-(k+1))+1 by omega,List.range'_succ]
  simp [program,parts,List.flatMap_append,List.append_assoc]

theorem round_fetch (s : Shape) (k : Nat) (hk : k < s.depth) :
    Fetches (program s) (22+16*k) (round s k) := by
  have fetch := fetches_slice (products s ++ (List.range k).flatMap (round s)) (round s k)
    ((List.range' (k+1) (s.depth-(k+1))).flatMap (round s) ++ output s)
  rw [← program_round_split s k hk] at fetch
  simpa [List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch

theorem round_run (s : Shape) (b : Bounds s) (k : Nat) (hk : k < s.depth)
    (state : Parallel.State s.threads) (t : Fin s.threads)
    (tid : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val)
    (column : (state.lanes t).scalar.regs 1 = BitVec.ofNat 32 (t.val%s.width))
    (shared : s.sharedWords ≤ state.shared.length)
    (pc : (state.lanes t).scalar.pc = 22+16*k)
    (live : (state.lanes t).halted = false) (fresh : state.barrier.arrived t = false) :
    ∃ events, Runs (config s b) (program s) state events (roundFinish s b k state t) := by
  have segment := segmentReference_sound (round_regular s b k hk state t tid column shared)
  refine ⟨_,segment.compile ?_ live fresh (by change 94=94 ∧ 70≤70; decide)⟩
  rw [pc]
  intro j hj
  have bound : j < 15 := by simpa using hj
  rw [round_fetch s k hk j (by simp; omega)]
  simp [List.getElem?_take,bound]

end Ptx.Scalar.Parallel.Dense
