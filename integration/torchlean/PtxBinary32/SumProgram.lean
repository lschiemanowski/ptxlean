import PtxBinary32.DenseLaunchContract

/-! A parallel sum reuses the fetched dense instruction list with one row,
unit weights and a positive-zero bias. These neutral operations remain real
instructions; numerical theorems separately explain their real-valued meaning. -/
namespace Ptx.Scalar.Parallel.Sum
open Ptx.Binary32

def width (d : Nat) : Nat := 2^d

def shape (d : Nat) : Dense.Shape := ⟨1,width d,d,le_rfl,false⟩

def Bounds (d : Nat) : Prop := d ≤ 10

/-- Inputs, unit weights, positive-zero bias and an allocated output cell. -/
def global (d : Nat) (input : Fin (width d) → Word) : List Word :=
  List.ofFn input ++ List.replicate (width d) 0x3f800000 ++ [0,0]

def outputIndex (d : Nat) : Nat := 2*width d+1

def sharedWords (d : Nat) : Nat := (d+1)*width d

def program (d : Nat) : List Instr := Dense.program (shape d)

@[simp] theorem threads_eq (d : Nat) : (shape d).threads=width d := by
  simp [shape,Dense.Shape.threads,Dense.Shape.width,width]

@[simp] theorem outputBase_eq (d : Nat) : (shape d).outputBase=outputIndex d := by
  simp [shape,Dense.Shape.outputBase,Dense.Shape.biasBase,outputIndex]; omega

@[simp] theorem globalWords_eq (d : Nat) : (shape d).globalWords=2*width d+2 := by
  simp [Dense.Shape.globalWords,shape,Dense.Shape.outputBase,Dense.Shape.biasBase]; omega

@[simp] theorem sharedWords_eq (d : Nat) : (shape d).sharedWords=sharedWords d := by
  simp only [Dense.Shape.sharedWords,threads_eq]; rfl

@[simp] theorem global_length (d : Nat) (input : Fin (width d) → Word) :
    (global d input).length=2*width d+2 := by simp [global]; omega

@[simp] theorem global_input (d : Nat) (input : Fin (width d) → Word) (j : Fin (width d)) :
    (global d input)[j.val]?=some (input j) := by
  simp [global,List.getElem?_append,j.isLt]

@[simp] theorem global_input_bang (d : Nat) (input : Fin (width d) → Word) (j : Nat) (hj : j<width d) :
    (global d input)[j]! = (List.ofFn input)[j]! := by
  simp [global,List.getElem!_eq_getElem?_getD,List.getElem?_append,hj]

@[simp] theorem global_weight (d : Nat) (input : Fin (width d) → Word) (j : Nat) (hj : j<width d) :
    (global d input)[width d+j]! = 0x3f800000 := by
  simp [global,List.getElem!_eq_getElem?_getD,List.getElem?_append,Nat.not_lt.mpr (Nat.le_add_right _ _),hj]

@[simp] theorem global_bias (d : Nat) (input : Fin (width d) → Word) :
    (global d input)[2*width d]! = 0 := by
  have h : ¬ 2*width d < width d := by omega
  simp [global,List.getElem!_eq_getElem?_getD,List.getElem?_append,h,show 2*width d-width d=width d by omega]

/-- Both allocation arithmetic and the selected 1024-thread limit follow from
this component's single depth bound. -/
theorem denseBounds (d : Nat) (bound : Bounds d) : Dense.Bounds (shape d) := by
  have small : width d ≤ 1024 := by
    unfold width
    exact le_trans (Nat.pow_le_pow_right (by decide) bound) (by norm_num)
  constructor
  · simp [shape]
  · change d<32; unfold Bounds at bound; omega
  · simpa using small
  · rw [globalWords_eq,sharedWords_eq]
    change 2*width d+2+(d+1)*width d+2*width d < 2^30
    unfold Bounds at bound
    nlinarith

theorem program_length (d : Nat) : (program d).length=42+16*d :=
  Dense.program_length (shape d)

/-- The exact ordered arithmetic contract, including the fetched unit products
and the final addition of positive zero. It does not exclude exceptional words. -/
def Output (d : Nat) (input : Fin (width d) → Word) (value : Word) : Prop :=
  ∃ dot, Reduction.Eval (Reduction.balanced d 0
    (fun j => (0x3f800000,(List.ofFn input)[j]!))) dot ∧ Results .add dot 0 value

private theorem balanced_congr (d offset : Nat) (a b : Nat → α)
    (same : ∀ j, offset≤j → j<offset+2^d → a j=b j) :
    Reduction.balanced d offset a=Reduction.balanced d offset b := by
  induction d generalizing offset with
  | zero => simp [Reduction.balanced,same offset (by omega) (by simp)]
  | succ d ih =>
    simp only [Reduction.balanced]
    congr 1
    · apply ih; intro j lo hi; apply same j lo
      rw [pow_succ] at *; omega
    · apply ih; intro j lo hi; apply same j (by omega)
      rw [pow_succ] at *; omega

/-- Specializing the existing kernel changes its operands, not its execution
semantics or its memory-admission requirement. -/
theorem output_iff (d : Nat) (input : Fin (width d) → Word) (value : Word) :
    Dense.Output (shape d) (global d input) 0 value ↔ Output d input value := by
  have operands : Reduction.balanced d 0 (Dense.operands (shape d) (global d input) 0) =
      Reduction.balanced d 0 (fun j => (0x3f800000,(List.ofFn input)[j]!)) := by
    apply balanced_congr
    intro j _ hj
    have h : j<width d := by simpa [width] using hj
    simp only [Dense.operands,shape,h,ite_true,Dense.Shape.weight,Dense.Shape.weightBase,Nat.zero_mul,Nat.add_zero]
    exact Prod.ext (global_weight d input j h) (global_input_bang d input j h)
  simp only [Dense.Output,Dense.Node,shape,Dense.activate,Bool.false_eq_true,ite_false,
    Nat.zero_mul]
  change (∃ dot affine, Reduction.Eval (Reduction.balanced d 0
      (Dense.operands (shape d) (global d input) 0)) dot ∧
      Results .add dot (global d input)[width d+1*width d+0]! affine ∧ value=affine) ↔ _
  rw [operands]
  have idx : width d+1*width d+0=2*width d := by omega
  rw [idx,global_bias]
  simp [Output]

end Ptx.Scalar.Parallel.Sum
