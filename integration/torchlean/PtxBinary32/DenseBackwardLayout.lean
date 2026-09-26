import PtxBinary32.DenseLaunchContract
import PtxBinary32.PointwiseLaunch

/-! Explicit buffers for the separately authored backward. The copy launch
constructs the transposed reduction packet from earlier actual storage. Appending
fresh zero storage and selecting an allocation view are host-model operations;
all gradient arithmetic and the operand rearrangement execute instructions. -/
namespace Ptx.Scalar.Parallel.DenseBackward

structure Shape where
  forward : Dense.Shape
  relu : forward.relu=true
  depth : Nat
  padded : forward.rows≤2^depth

abbrev Shape.rows (s : Shape) := s.forward.rows
abbrev Shape.columns (s : Shape) := s.forward.columns

def Shape.transposed (s : Shape) : Dense.Shape :=
  ⟨s.columns,s.rows,s.depth,s.padded,false⟩

def Shape.gateBase (s : Shape) := s.forward.globalWords+s.rows
def Shape.weightBase (s : Shape) := s.gateBase+s.rows
def Shape.weightCount (s : Shape) := s.rows*s.columns
def Shape.copyBase (s : Shape) := s.weightBase+s.weightCount+1

structure Bounds (s : Shape) : Prop where
  forward : 0<s.rows → Dense.Bounds s.forward
  transposed : 0<s.columns → Dense.Bounds s.transposed
  copyThreads : s.transposed.globalWords≤1024
  small : s.copyBase+s.transposed.globalWords<2^30

private theorem rows_small (s : Shape) (b : Bounds s) : s.rows≤1024 := by
  by_cases h : 0<s.rows
  · have threads := (b.forward h).threads
    have width := Dense.width_positive s.forward
    change s.rows*s.forward.width≤1024 at threads
    nlinarith
  · omega

private theorem weights_small (s : Shape) (b : Bounds s) : s.weightCount≤1024 := by
  by_cases h : 0<s.rows
  · have threads := (b.forward h).threads
    have pad := s.forward.padded
    have mono := Nat.mul_le_mul_left s.rows pad
    exact le_trans mono threads
  · have zero : s.rows=0 := by omega
    simp [Shape.weightCount,zero]

def gateLayout (s : Shape) (b : Bounds s) : Pointwise.Layout s.rows where
  prefixWords := s.gateBase
  left t := s.forward.outputBase+t.val
  right t := s.forward.globalWords+t.val
  leftBound t := by have := t.isLt; unfold Shape.gateBase Dense.Shape.globalWords; omega
  rightBound t := by have := t.isLt; unfold Shape.gateBase; omega
  small := by have := b.small; unfold Shape.copyBase Shape.weightBase at this; omega

def weightLayout (s : Shape) (b : Bounds s) : Pointwise.Layout s.weightCount where
  prefixWords := s.weightBase
  left t := s.gateBase+t.val/s.columns
  right t := t.val%s.columns
  leftBound t := by
    have ht := t.isLt
    change t.val<s.rows*s.columns at ht
    have pos : 0<s.columns := by by_contra no; have z : s.columns=0 := (by omega); simp [z] at ht
    have row : t.val/s.columns<s.rows := (Nat.div_lt_iff_lt_mul pos).mpr ht
    unfold Shape.weightBase; omega
  rightBound t := by
    have ht := t.isLt
    change t.val<s.rows*s.columns at ht
    have pos : 0<s.columns := by by_contra no; have z : s.columns=0 := (by omega); simp [z] at ht
    have col := Nat.mod_lt t.val pos
    unfold Shape.weightBase Shape.gateBase Dense.Shape.globalWords Dense.Shape.outputBase Dense.Shape.biasBase
    change t.val%s.columns<s.columns+s.rows*s.columns+s.rows+s.rows+s.rows+s.rows
    omega
  small := by have := b.small; unfold Shape.copyBase at this; omega

def copySource (s : Shape) (i : Nat) : Nat :=
  if i<s.rows then s.gateBase+i else
  if i<s.transposed.biasBase then
    s.forward.weight ((i-s.rows)%s.rows) ((i-s.rows)/s.rows)
  else s.copyBase-1

theorem copy_source_bound (s : Shape) (i : Nat) : copySource s i<s.copyBase := by
  unfold copySource
  split
  · unfold Shape.copyBase Shape.weightBase; omega
  · rename_i notInput
    split
    · rename_i matrix
      have matrixBound : i<s.rows+s.columns*s.rows := matrix
      have pos : 0<s.rows := by by_contra h; have z : s.rows=0 := (by omega); simp [z] at matrixBound
      have row := Nat.mod_lt (i-s.rows) pos
      have column : (i-s.rows)/s.rows<s.columns := (Nat.div_lt_iff_lt_mul pos).mpr (by omega)
      have bound := Dense.weight_bound s.forward _ _ row column
      unfold Shape.copyBase Shape.weightBase Shape.gateBase Dense.Shape.globalWords Dense.Shape.outputBase
      omega
    · unfold Shape.copyBase; omega

def copyLayout (s : Shape) (b : Bounds s) : Pointwise.Layout s.transposed.globalWords where
  prefixWords := s.copyBase
  left t := copySource s t.val
  right t := copySource s t.val
  leftBound t := copy_source_bound s t.val
  rightBound t := copy_source_bound s t.val
  small := b.small

def gateInput (s : Shape) (forward : List Word) (incoming : Fin s.rows → Word) : List Word :=
  forward ++ List.ofFn incoming ++ List.replicate s.rows 0

def weightInput (s : Shape) (gated : List Word) : List Word :=
  gated ++ List.replicate s.weightCount 0

def copyInput (s : Shape) (weighted : List Word) : List Word :=
  weighted ++ [0] ++ List.replicate s.transposed.globalWords 0

def packet (s : Shape) (copied : List Word) : List Word := copied.drop s.copyBase

/-- All stages are actual completed admitted launches. Later launch inputs are
functions of earlier final arrays, never supplied arithmetic results. -/
structure Execution (s : Shape) (b : Bounds s) (before : List Word) (incoming : Fin s.rows → Word) where
  forward : List Word
  gated : List Word
  weighted : List Word
  copied : List Word
  inputGradient : List Word
  forwardRun : Dense.Launch s.forward before forward
  gateRun : Pointwise.Launch .gate (gateLayout s b) (gateInput s forward incoming) gated
  weightRun : Pointwise.Launch .mul (weightLayout s b) (weightInput s gated) weighted
  copyRun : Pointwise.Launch .copy (copyLayout s b) (copyInput s weighted) copied
  inputRun : Dense.Launch s.transposed (packet s copied) inputGradient

theorem execution_exists (s : Shape) (b : Bounds s) (before : List Word) (incoming : Fin s.rows → Word)
    (size : before.length=s.forward.globalWords) : Nonempty (Execution s b before incoming) := by
  obtain ⟨forward,forwardRun⟩ := Dense.launch_exists s.forward before b.forward (by omega)
  have fl := (Dense.launch_correct forwardRun).2.2
  obtain ⟨gated,gateRun⟩ := Pointwise.launch_exists .gate (gateLayout s b) (gateInput s forward incoming)
    (rows_small s b) (by simp [gateLayout,gateInput,Shape.gateBase,fl,size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])
  have gl := (Pointwise.launch_correct gateRun).2.2
  obtain ⟨weighted,weightRun⟩ := Pointwise.launch_exists .mul (weightLayout s b) (weightInput s gated)
    (weights_small s b) (by simp [weightLayout,weightInput,Shape.weightBase,Shape.gateBase,gl,gateInput,fl,size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])
  have wl := (Pointwise.launch_correct weightRun).2.2
  obtain ⟨copied,copyRun⟩ := Pointwise.launch_exists .copy (copyLayout s b) (copyInput s weighted)
    b.copyThreads (by simp [copyLayout,copyInput,Shape.copyBase,Shape.weightBase,Shape.gateBase,wl,weightInput,gl,gateInput,fl,size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])
  have cl := (Pointwise.launch_correct copyRun).2.2
  have pl : (packet s copied).length=s.transposed.globalWords := by
    simp [packet,cl,copyInput,wl,weightInput,gl,gateInput,fl,size,Shape.copyBase,Shape.weightBase,Shape.gateBase]
    omega
  obtain ⟨dx,dxRun⟩ := Dense.launch_exists s.transposed (packet s copied) b.transposed (by omega)
  exact ⟨⟨forward,gated,weighted,copied,dx,forwardRun,gateRun,weightRun,copyRun,dxRun⟩⟩

end Ptx.Scalar.Parallel.DenseBackward
