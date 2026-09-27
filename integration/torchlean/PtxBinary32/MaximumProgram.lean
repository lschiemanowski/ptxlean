import PtxBinary32.MaximumSelect
import PtxBinary32.MaximumTree
import PtxBinary32.DenseSegments
import PtxBinary32.ParallelBarrier
import PtxBinary32.ParallelAdmission

/-! One power-of-two row, one thread per input, fresh shared planes. All address
calculations, transfers, comparisons, barriers and exits are fetched instructions. -/
namespace Ptx.Scalar.Parallel.Maximum

abbrev width (depth : Nat) : Nat := 2^depth
abbrev sharedWords (depth : Nat) : Nat := (depth+1)*width depth

def Bounds (depth : Nat) : Prop := width depth ≤ 1024

def config (depth : Nat) : Config (width depth) := ⟨⟨94,70⟩,0,Nat.two_pow_pos _⟩

def initial (depth : Nat) (global shared : List Word) (seeds : Fin (width depth) → Scalar.State) : State (width depth) :=
  ⟨fun t => ⟨{seeds t with pc := 0,regs := Scalar.update (seeds t).regs 0 (BitVec.ofNat 32 t.val)},false⟩,
    global,shared,Barrier.reset 0,none⟩

abbrev word := Dense.word
abbrev scalar := Dense.scalar
abbrev guarded := Dense.guarded
abbrev pointer := Dense.pointer

/-- Publish each input. Register zero is the supplied thread identity. -/
def publishCode : List Instr := pointer 0 0 ++ [
  .memory .global (.plain (.load 4 (.reg 0))),
  .memory .shared (.plain (.store (.reg 0) (.reg 4)))]
def publish : List Instr := publishCode ++ [.sync 0]

/-- Inactive threads still execute integer scratch computations, then skip
memory accesses and reach the same unconditional barrier. -/
def roundPrefix (depth k : Nat) : List Instr := [
  scalar (.setp .lt 0 (.reg 0) (word (2^(depth-(k+1))))),
  scalar (.bin32 .add 7 (.reg 0) (.reg 0)),
  scalar (.bin32 .add 7 (.reg 7) (word (k*width depth)))] ++
  pointer 1 7 ++ [scalar (.add64 2 (.reg 1) (.imm 4)),
  guarded .shared (.load 4 (.reg 1)),guarded .shared (.load 5 (.reg 2))]

def roundSuffix (depth k : Nat) : List Instr := [
  scalar (.bin32 .add 7 (.reg 0) (word ((k+1)*width depth)))] ++
  pointer 3 7 ++ [guarded .shared (.store (.reg 3) (.reg 6))]

def roundCode (depth k : Nat) : List Instr :=
  roundPrefix depth k ++ Scalar.MaximumSelect.code ++ roundSuffix depth k

def round (depth k : Nat) : List Instr := roundCode depth k ++ [.sync 0]

def outputCode (depth : Nat) : List Instr := [
  scalar (.setp .eq 0 (.reg 0) (word 0)),
  scalar (.mov32 7 (word (depth*width depth)))] ++ pointer 0 7 ++ [
  guarded .shared (.load 6 (.reg 0)),scalar (.mov32 7 (word (width depth)))] ++
  pointer 1 7 ++ [guarded .global (.store (.reg 1) (.reg 6))]

def output (depth : Nat) : List Instr := outputCode depth ++ [.exit]

def program (depth : Nat) : List Instr :=
  publish ++ (List.range depth).flatMap (round depth) ++ output depth

@[simp] theorem publishCode_length : publishCode.length=5 := by simp [publishCode,Dense.pointer]
@[simp] theorem publish_length : publish.length=6 := by simp [publish]
@[simp] theorem roundPrefix_length (d k : Nat) : (roundPrefix d k).length=9 := by simp [roundPrefix,Dense.pointer]
@[simp] theorem roundSuffix_length (d k : Nat) : (roundSuffix d k).length=5 := by simp [roundSuffix,Dense.pointer]
@[simp] theorem roundCode_length (d k : Nat) : (roundCode d k).length=23 := by simp [roundCode,Scalar.MaximumSelect.code_length]
@[simp] theorem round_length (d k : Nat) : (round d k).length=24 := by simp [round]
@[simp] theorem outputCode_length (d : Nat) : (outputCode d).length=11 := by simp [outputCode,Dense.pointer]
@[simp] theorem output_length (d : Nat) : (output d).length=12 := by simp [output]
@[simp] theorem program_length (d : Nat) : (program d).length=18+24*d := by
  simp [program,List.length_flatMap,List.sum_replicate,Nat.mul_comm,Nat.add_comm]
  omega

theorem bounds_depth (b : Bounds d) : d≤10 := by
  by_contra h
  have p := Nat.pow_le_pow_right (n:=2) (by decide) (show 11≤d by omega)
  change 2048≤width d at p
  unfold Bounds at b
  omega

theorem width_fits (b : Bounds d) : width d < 2^32 := by unfold Bounds at b; omega

theorem shared_fits (b : Bounds d) : sharedWords d < 2^32 := by
  have hd := bounds_depth b
  have hw : width d ≤1024 := b
  have bound := Nat.mul_le_mul (show d+1≤11 by omega) hw
  change (d+1)*width d<4294967296
  omega

theorem children_bound (k d t : Nat) (hk : k<d) (active : t<2^(d-(k+1))) :
    2*t<2^(d-k) ∧ 2*t+1<2^(d-k) := by
  have eq : d-k=(d-(k+1))+1 := by omega
  rw [eq,pow_succ]
  omega

theorem plane_bound (depth k t : Nat) (hk : k≤depth) (ht : t<width depth) :
    k*width depth+t<sharedWords depth := by
  have h := Nat.mul_le_mul_right (width depth) hk
  unfold sharedWords
  rw [Nat.add_mul]
  omega

theorem publish_fetch (d : Nat) : Fetches (program d) 0 publish := by
  simpa [program,List.append_assoc] using fetches_slice [] publish ((List.range d).flatMap (round d) ++ output d)

theorem program_round_split (d k : Nat) (hk : k<d) :
    program d=(publish ++ (List.range k).flatMap (round d)) ++ round d k ++
      ((List.range' (k+1) (d-(k+1))).flatMap (round d) ++ output d) := by
  have cut := List.range'_append_1 (s:=0) (m:=k) (n:=d-k)
  simp only [Nat.zero_add,show k+(d-k)=d by omega] at cut
  have parts : List.range d=List.range k ++ k::List.range' (k+1) (d-(k+1)) := by
    rw [List.range_eq_range',←cut]
    simp [List.range_eq_range',show d-k=(d-(k+1))+1 by omega,List.range'_succ]
  simp [program,parts,List.flatMap_append,List.append_assoc]

theorem round_fetch (d k : Nat) (hk : k<d) : Fetches (program d) (6+24*k) (round d k) := by
  have f := fetches_slice (publish ++ (List.range k).flatMap (round d)) (round d k)
    ((List.range' (k+1) (d-(k+1))).flatMap (round d) ++ output d)
  rw [←program_round_split d k hk] at f
  simpa [List.length_flatMap,List.sum_replicate,Nat.mul_comm] using f

theorem output_fetch (d : Nat) : Fetches (program d) (6+24*d) (output d) := by
  have f := fetches_slice (publish ++ (List.range d).flatMap (round d)) (output d) []
  simpa [program,List.length_flatMap,List.sum_replicate,Nat.mul_comm] using f

end Ptx.Scalar.Parallel.Maximum
