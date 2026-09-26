import PtxBinary32.DenseLocalSegments

/-! Compact per-group dense scratch. Arithmetic contracts are shared with Dense;
only the fetched shared addresses and their allocation change. -/
namespace Ptx.Scalar.Parallel.Dense.Compact
def sharedWords (s : Shape) : Nat := (s.depth+1)*s.width

/-- The former per-group extent paid one extra factor equal to the row count. -/
theorem shared_words_factor (s : Shape) : s.sharedWords=s.rows*sharedWords s := by
  simp only [Shape.sharedWords,Shape.threads,sharedWords]
  ring

/-- Each fresh plane is a full local row; no offset depends on a global row. -/
theorem scratch_bound (s : Shape) (k c : Nat) (hk : k≤s.depth) (hc : c<s.width) :
    k*s.width+c<sharedWords s := by
  have h := Nat.mul_le_mul_right s.width hk
  simp only [sharedWords,Nat.add_mul,Nat.one_mul]
  omega

def leftIndex (s : Shape) (k : Nat) (t : Fin s.threads) : Nat := t.val%s.width+t.val%s.width+k*s.width
def nextIndex (s : Shape) (k : Nat) (t : Fin s.threads) : Nat := t.val%s.width+(k+1)*s.width
def rootIndex (s : Shape) (t : Fin s.threads) : Nat := t.val%s.width+s.depth*s.width

theorem shared_le (s : Shape) (t : Fin s.threads) : sharedWords s≤s.sharedWords := by
  have rows : 1≤s.rows := Nat.succ_le_iff.mpr (lt_of_le_of_lt (Nat.zero_le _) (coordinates s t).1)
  have width : s.width≤s.threads := by
    simpa [Shape.threads] using Nat.mul_le_mul_right s.width rows
  exact Nat.mul_le_mul_left _ width

theorem round_indices (s : Shape) (b : ArithmeticBounds s) (k : Nat) (hk : k<s.depth) (t : Fin s.threads) :
    leftIndex s k t<2^32 ∧ nextIndex s k t<sharedWords s ∧
      (t.val%s.width<2^(s.depth-(k+1)) → leftIndex s k t+1<sharedWords s) := by
  have col := (coordinates s t).2.1
  have next : (k+1)*s.width≤s.depth*s.width := Nat.mul_le_mul_right s.width hk
  have plane := Nat.mul_le_mul_right s.width (Nat.le_of_lt hk)
  have bound := b.arithmetic
  have small := shared_le s t
  have extent : sharedWords s=s.depth*s.width+s.width := by simp [sharedWords,Nat.add_mul]
  refine ⟨by dsimp [leftIndex]; omega,by dsimp [nextIndex]; omega,?_⟩
  intro active
  have child := (children_bound s k _ hk active).2
  have width : 2^(s.depth-k)≤s.width := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  dsimp [leftIndex]; omega

theorem output_indices (s : Shape) (t : Fin s.threads) :
    rootIndex s t<sharedWords s ∧ biasIndex s t<s.outputBase ∧
      s.outputBase≤outputIndex s t ∧ outputIndex s t<s.globalWords := by
  refine ⟨?_,(Dense.output_indices s t).2⟩
  have := (coordinates s t).2.1
  simp only [rootIndex,sharedWords,Nat.add_mul,Nat.one_mul]
  omega

def products (s : Shape) : List Parallel.Instr := [
  scalar (.bin32 .and 1 (.reg 0) (word (s.width-1))),
  scalar (.bin32 .shr 2 (.reg 0) (word s.depth)),
  scalar (.bin32 .mulLo 3 (.reg 2) (word s.columns)),
  scalar (.bin32 .add 3 (.reg 3) (.reg 1)),
  scalar (.bin32 .add 3 (.reg 3) (word s.weightBase)),
  scalar (.setp .lt 0 (.reg 1) (word s.columns)),
  scalar (.mov32 4 (word 0)), scalar (.mov32 5 (word 0))] ++
  pointer 0 1 ++ [guarded .global (.load 4 (.reg 0))] ++
  pointer 1 3 ++ [guarded .global (.load 5 (.reg 1)),
  .binary32 ⟨.always,.mul,6,.reg 5,.reg 4⟩] ++
  pointer 2 1 ++ [.memory .shared (.plain (.store (.reg 2) (.reg 6))),.sync 0]

def round (s : Shape) (k : Nat) : List Parallel.Instr := [
  scalar (.setp .lt 0 (.reg 1) (word (2^(s.depth-(k+1))))),
  scalar (.bin32 .add 7 (.reg 1) (.reg 1)),
  scalar (.bin32 .add 7 (.reg 7) (word (k*s.width)))] ++
  pointer 3 7 ++ [scalar (.add64 4 (.reg 3) (.imm 4)),
  guarded .shared (.load 4 (.reg 3)), guarded .shared (.load 5 (.reg 4)),
  .binary32 ⟨.pred 0 true,.add,6,.reg 4,.reg 5⟩,
  scalar (.bin32 .add 7 (.reg 1) (word ((k+1)*s.width)))] ++
  pointer 2 7 ++ [guarded .shared (.store (.reg 2) (.reg 6)),.sync 0]

def output (s : Shape) : List Parallel.Instr := [
  scalar (.setp .eq 0 (.reg 1) (word 0)),
  scalar (.bin32 .add 7 (.reg 1) (word (s.depth*s.width)))] ++
  pointer 2 7 ++ [guarded .shared (.load 6 (.reg 2)),
  scalar (.bin32 .add 7 (.reg 2) (word s.biasBase))] ++
  pointer 5 7 ++ [guarded .global (.load 8 (.reg 5)),
  .binary32 ⟨.pred 0 true,.add,6,.reg 6,.reg 8⟩,
  scalar (.setp .ge 1 (.reg 6) (word 0x80000000)),
  .localStep ⟨.pred 1 true,.mov32 6 (if s.relu then word 0 else .reg 6)⟩,
  scalar (.bin32 .add 7 (.reg 2) (word s.outputBase))] ++
  pointer 6 7 ++ [guarded .global (.store (.reg 6) (.reg 6)),.exit]

def program (s : Shape) : List Parallel.Instr :=
  products s ++ (List.range s.depth).flatMap (round s) ++ output s

@[simp] theorem products_length (s : Shape) : (products s).length = 22 := by simp [products,pointer]
@[simp] theorem round_length (s : Shape) (k : Nat) : (round s k).length = 16 := by simp [round,pointer]
@[simp] theorem output_length (s : Shape) : (output s).length = 20 := by simp [output,pointer]

theorem program_length (s : Shape) : (program s).length = 42+16*s.depth := by
  simp [program,List.length_flatMap,List.sum_replicate,Nat.mul_comm,Nat.add_comm]

/-- Each round's barrier is unconditional, including for inactive columns. -/
theorem round_barrier (s : Shape) (k : Nat) : (round s k)[15]? = some (.sync 0) := rfl

theorem product_barrier (s : Shape) : (products s)[21]? = some (.sync 0) := rfl

theorem output_exit (s : Shape) : (output s)[19]? = some .exit := rfl

theorem products_fetch (s : Shape) : Fetches (program s) 0 ((products s).take 21) := by
  intro k hk
  have bound : k < 21 := by simpa using hk
  have inside : k < (products s).length := by rw [products_length]; omega
  have h22 : k < 22 := by omega
  simp [program,List.getElem?_append,inside,List.getElem?_take,bound,h22]

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

theorem output_fetch (s : Shape) : Fetches (program s) (22+16*s.depth) (output s) := by
  have fetch := fetches_slice (products s ++ (List.range s.depth).flatMap (round s)) (output s) []
  simpa [program,List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch


end Ptx.Scalar.Parallel.Dense.Compact
