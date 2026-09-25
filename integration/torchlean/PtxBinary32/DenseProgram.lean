import PtxBinary32.DenseLayout
import PtxBinary32.ParallelReference
import PtxBinary32.Relu

/-! A separately authored, shape-specialized dense forward instruction list.
All rows reside in one CTA. No abstract reduction or ReLU operation is inserted
into the machine: address arithmetic, loads, stores, gates and barriers are
ordinary fetched instructions. Launch/ABI validation is a separate obligation. -/
namespace Ptx.Scalar.Parallel.Dense

def word (n : Nat) : Scalar.Operand32 := .imm (BitVec.ofNat 32 n)
def scalar (op : Scalar.Op) : Parallel.Instr := .localStep (.plain op)
def guarded (space : Space) (op : Scalar.Op) : Parallel.Instr := .memory space ⟨.pred 0 true,op⟩

/-- Convert a word index to a byte pointer using three represented instructions. -/
def pointer (destination source : Nat) : List Parallel.Instr := [
  scalar (.cvt64 destination (.reg source)),
  scalar (.add64 destination (.reg destination) (.reg destination)),
  scalar (.add64 destination (.reg destination) (.reg destination))]

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
  pointer 2 0 ++ [.memory .shared (.plain (.store (.reg 2) (.reg 6))),.sync 0]

def round (s : Shape) (k : Nat) : List Parallel.Instr := [
  scalar (.setp .lt 0 (.reg 1) (word (2^(s.depth-(k+1))))),
  scalar (.bin32 .add 7 (.reg 0) (.reg 1)),
  scalar (.bin32 .add 7 (.reg 7) (word (k*s.threads)))] ++
  pointer 3 7 ++ [scalar (.add64 4 (.reg 3) (.imm 4)),
  guarded .shared (.load 4 (.reg 3)), guarded .shared (.load 5 (.reg 4)),
  .binary32 ⟨.pred 0 true,.add,6,.reg 4,.reg 5⟩,
  scalar (.bin32 .add 7 (.reg 0) (word ((k+1)*s.threads)))] ++
  pointer 2 7 ++ [guarded .shared (.store (.reg 2) (.reg 6)),.sync 0]

def output (s : Shape) : List Parallel.Instr := [
  scalar (.setp .eq 0 (.reg 1) (word 0)),
  scalar (.bin32 .add 7 (.reg 0) (word (s.depth*s.threads)))] ++
  pointer 2 7 ++ [guarded .shared (.load 6 (.reg 2)),
  scalar (.bin32 .add 7 (.reg 2) (word s.biasBase))] ++
  pointer 5 7 ++ [guarded .global (.load 8 (.reg 5)),
  .binary32 ⟨.pred 0 true,.add,6,.reg 6,.reg 8⟩,
  scalar (.setp .ge 1 (.reg 6) (word 0x80000000)),
  .localStep ⟨.pred 1 true,.mov32 6 (word 0)⟩,
  scalar (.bin32 .add 7 (.reg 2) (word s.outputBase))] ++
  pointer 6 7 ++ [guarded .global (.store (.reg 6) (.reg 6)),.exit]

def program (s : Shape) : List Parallel.Instr :=
  products s ++ (List.range s.depth).flatMap (round s) ++ output s

/-- Deliberately bounded first implementation. The resource cap is a selected
kernel domain, not a theorem that every listed shape launches on every GPU. -/
structure Bounds (s : Shape) : Prop where
  nonempty : 0 < s.rows
  depth : s.depth < 32
  threads : s.threads ≤ 1024
  arithmetic : s.globalWords+s.sharedWords+2*s.width < 2^30

def config (s : Shape) (bounds : Bounds s) : Config s.threads :=
  ⟨⟨94,70⟩,0,Nat.mul_pos bounds.nonempty (width_positive s)⟩

/-- Only thread IDs and entry PC are installed. All other registers come from
caller seeds; kernel instructions must initialize any value they depend on. -/
def initial (s : Shape) (global shared : List Word) (seeds : Fin s.threads → Scalar.State) :
    Parallel.State s.threads :=
  ⟨fun t => ⟨{seeds t with pc := 0,regs := Scalar.update (seeds t).regs 0 (BitVec.ofNat 32 t.val)},false⟩,
    global,shared,Barrier.reset 0,none⟩

@[simp] theorem products_length (s : Shape) : (products s).length = 22 := by simp [products,pointer]
@[simp] theorem round_length (s : Shape) (k : Nat) : (round s k).length = 16 := by simp [round,pointer]
@[simp] theorem output_length (s : Shape) : (output s).length = 20 := by simp [output,pointer]

theorem program_length (s : Shape) : (program s).length = 42+16*s.depth := by
  simp [program,List.length_flatMap,List.sum_replicate,Nat.mul_comm,Nat.add_comm]

/-- Each round's barrier is unconditional, including for inactive columns. -/
theorem round_barrier (s : Shape) (k : Nat) : (round s k)[15]? = some (.sync 0) := rfl

theorem product_barrier (s : Shape) : (products s)[21]? = some (.sync 0) := rfl

theorem output_exit (s : Shape) : (output s)[19]? = some .exit := rfl

/-- The forward sign test canonicalizes both signs of zero to positive zero.
For exceptional encodings this remains a bit-level operation, not real ReLU. -/
theorem relu_bits (a : Word) :
    (if a.toNat ≥ 2147483648 then (0 : Word) else a) = Ptx.Binary32.Relu.forward a := by
  unfold Ptx.Binary32.Relu.forward Ptx.Binary32.Relu.gate Ptx.Binary32.Relu.positive
  by_cases zero : a = 0
  · subst a; rfl
  · have pos : 0 < a.toNat := by
      have ne : a.toNat ≠ 0 := by intro h; exact zero (BitVec.eq_of_toNat_eq h)
      omega
    by_cases sign : a.toNat ≥ 2147483648 <;> simp [pos,sign,show a.toNat < 2147483648 ↔ ¬a.toNat ≥ 2147483648 by omega]

end Ptx.Scalar.Parallel.Dense
