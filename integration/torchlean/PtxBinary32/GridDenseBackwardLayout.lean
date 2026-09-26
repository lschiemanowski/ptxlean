import PtxBinary32.DenseBackwardLayout
import PtxBinary32.GridDenseLaunch
import PtxBinary32.GridPointwiseLogical

/-! Explicit buffers for the separately authored backward. The copy launch
constructs the transposed reduction packet from earlier actual storage. Appending
fresh zero storage and selecting an allocation view are host-model operations;
all gradient arithmetic and the operand rearrangement execute instructions. -/
namespace Ptx.Scalar.Parallel.GridDenseBackward

abbrev Shape := DenseBackward.Shape
open DenseBackward (Shape)

structure Bounds (s : Shape) : Prop where
  forward : 0<s.rows → GridDense.Bounds s.forward
  transposed : 0<s.columns → GridDense.Bounds s.transposed
  small : s.copyBase+s.transposed.globalWords+32<2^30

def gateLayout (s : Shape) (b : Bounds s) : Pointwise.Layout s.rows where
  prefixWords := s.gateBase
  left t := s.forward.outputBase+t.val
  right t := s.forward.globalWords+t.val
  leftBound t := by have := t.isLt; unfold DenseBackward.Shape.gateBase Dense.Shape.globalWords; omega
  rightBound t := by have := t.isLt; unfold DenseBackward.Shape.gateBase; omega
  small := by have := b.small; unfold DenseBackward.Shape.copyBase DenseBackward.Shape.weightBase at this; omega

def weightLayout (s : Shape) (b : Bounds s) : Pointwise.Layout s.weightCount where
  prefixWords := s.weightBase
  left t := s.gateBase+t.val/s.columns
  right t := t.val%s.columns
  leftBound t := by
    have ht := t.isLt
    change t.val<s.rows*s.columns at ht
    have pos : 0<s.columns := by by_contra no; have z : s.columns=0 := (by omega); simp [z] at ht
    have row : t.val/s.columns<s.rows := (Nat.div_lt_iff_lt_mul pos).mpr ht
    unfold DenseBackward.Shape.weightBase; omega
  rightBound t := by
    have ht := t.isLt
    change t.val<s.rows*s.columns at ht
    have pos : 0<s.columns := by by_contra no; have z : s.columns=0 := (by omega); simp [z] at ht
    have col := Nat.mod_lt t.val pos
    unfold DenseBackward.Shape.weightBase DenseBackward.Shape.gateBase Dense.Shape.globalWords Dense.Shape.outputBase Dense.Shape.biasBase
    change t.val%s.columns<s.columns+s.rows*s.columns+s.rows+s.rows+s.rows+s.rows
    omega
  small := by have := b.small; unfold DenseBackward.Shape.copyBase at this; omega

def copySource (s : Shape) (i : Nat) : Nat :=
  if i<s.rows then s.gateBase+i else
  if i<s.transposed.biasBase then
    s.forward.weight ((i-s.rows)%s.rows) ((i-s.rows)/s.rows)
  else s.copyBase-1

theorem copy_source_bound (s : Shape) (i : Nat) : copySource s i<s.copyBase := by
  unfold copySource
  split
  · unfold DenseBackward.Shape.copyBase DenseBackward.Shape.weightBase; omega
  · rename_i notInput
    split
    · rename_i matrix
      have matrixBound : i<s.rows+s.columns*s.rows := matrix
      have pos : 0<s.rows := by by_contra h; have z : s.rows=0 := (by omega); simp [z] at matrixBound
      have row := Nat.mod_lt (i-s.rows) pos
      have column : (i-s.rows)/s.rows<s.columns := (Nat.div_lt_iff_lt_mul pos).mpr (by omega)
      have bound := Dense.weight_bound s.forward _ _ row column
      unfold DenseBackward.Shape.copyBase DenseBackward.Shape.weightBase DenseBackward.Shape.gateBase Dense.Shape.globalWords Dense.Shape.outputBase
      omega
    · unfold DenseBackward.Shape.copyBase; omega

def copyLayout (s : Shape) (b : Bounds s) : Pointwise.Layout s.transposed.globalWords where
  prefixWords := s.copyBase
  left t := copySource s t.val
  right t := copySource s t.val
  leftBound t := copy_source_bound s t.val
  rightBound t := copy_source_bound s t.val
  small := by have := b.small; omega

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
  forwardRun : GridDense.Launch s.forward before forward
  gateRun : GridPointwise.LogicalLaunch .gate (gateLayout s b) (gateInput s forward incoming) gated
  weightRun : GridPointwise.LogicalLaunch .mul (weightLayout s b) (weightInput s gated) weighted
  copyRun : GridPointwise.LogicalLaunch .copy (copyLayout s b) (copyInput s weighted) copied
  inputRun : GridDense.Launch s.transposed (packet s copied) inputGradient

theorem execution_exists (s : Shape) (b : Bounds s) (before : List Word) (incoming : Fin s.rows → Word)
    (size : before.length=s.forward.globalWords) : Nonempty (Execution s b before incoming) := by
  obtain ⟨forward,forwardRun⟩ := GridDense.launch_exists s.forward before b.forward (by omega)
  have fl := (GridDense.launch_correct forwardRun).2.2
  obtain ⟨gated,gateRun⟩ := GridPointwise.logical_exists .gate (gateLayout s b) (gateInput s forward incoming)
    (by have := b.small; dsimp [gateLayout,DenseBackward.Shape.copyBase,DenseBackward.Shape.weightBase] at *; omega) (by simp [gateLayout,gateInput,DenseBackward.Shape.gateBase,fl,size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])
  have gl := (GridPointwise.logical_correct gateRun).2.2
  obtain ⟨weighted,weightRun⟩ := GridPointwise.logical_exists .mul (weightLayout s b) (weightInput s gated)
    (by have := b.small; dsimp [weightLayout,DenseBackward.Shape.copyBase] at *; omega) (by simp [weightLayout,weightInput,DenseBackward.Shape.weightBase,DenseBackward.Shape.gateBase,gl,gateInput,fl,size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])
  have wl := (GridPointwise.logical_correct weightRun).2.2
  obtain ⟨copied,copyRun⟩ := GridPointwise.logical_exists .copy (copyLayout s b) (copyInput s weighted)
    (by exact b.small) (by simp [copyLayout,copyInput,DenseBackward.Shape.copyBase,DenseBackward.Shape.weightBase,DenseBackward.Shape.gateBase,wl,weightInput,gl,gateInput,fl,size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])
  have cl := (GridPointwise.logical_correct copyRun).2.2
  have pl : (packet s copied).length=s.transposed.globalWords := by
    simp [packet,cl,copyInput,wl,weightInput,gl,gateInput,fl,size,DenseBackward.Shape.copyBase,DenseBackward.Shape.weightBase,DenseBackward.Shape.gateBase]
    omega
  obtain ⟨dx,dxRun⟩ := GridDense.launch_exists s.transposed (packet s copied) b.transposed (by omega)
  exact ⟨⟨forward,gated,weighted,copied,dx,forwardRun,gateRun,weightRun,copyRun,dxRun⟩⟩

end Ptx.Scalar.Parallel.GridDenseBackward
