import PtxBinary32.SumProgram
import PtxBinary32.PointwiseLaunch
import PtxBinary32.SoftmaxStorage

/-! Storage interfaces for backward: the dense dot product retains both input
rows. Fresh difference and gradient suffixes are allocated between completed
launches, without performing arithmetic in the composition model. -/
namespace Ptx.Scalar.Parallel.SoftmaxBackward

def differenceBase (d : Nat) := 2*Sum.width d+2
def gradientBase (d : Nat) := 3*Sum.width d+2

theorem width_bound (d : Nat) (bound : Sum.Bounds d) : Sum.width d≤1024 := by
  simpa using (Sum.denseBounds d bound).threads

def differenceLayout (d : Nat) (bound : Sum.Bounds d) : Pointwise.Layout (Sum.width d) where
  prefixWords := differenceBase d
  left := fun i => Sum.width d+i.val
  right := fun _ => Sum.outputIndex d
  leftBound := by intro i; have := i.isLt; unfold differenceBase; omega
  rightBound := by intro i; unfold differenceBase Sum.outputIndex; omega
  small := by have := width_bound d bound; unfold differenceBase; omega

def gradientLayout (d : Nat) (bound : Sum.Bounds d) : Pointwise.Layout (Sum.width d) where
  prefixWords := gradientBase d
  left := fun i => i.val
  right := fun i => differenceBase d+i.val
  leftBound := by intro i; have := i.isLt; unfold gradientBase; omega
  rightBound := by intro i; have := i.isLt; unfold differenceBase gradientBase; omega
  small := by have := width_bound d bound; unfold gradientBase; omega

def extend (d : Nat) (before : List Word) := before++List.replicate (Sum.width d) 0

@[simp] theorem extend_length (d : Nat) (before : List Word) :
    (extend d before).length=before.length+Sum.width d := by simp [extend]

theorem extend_prefix (d : Nat) (before : List Word) (i : Nat) (inside : i<before.length) :
    (extend d before)[i]?=before[i]? := by simp [extend,List.getElem?_append,inside]

theorem bang_eq (a b : List Word) (i : Nat) (same : a[i]?=b[i]?) : a[i]! =b[i]! := by
  simp only [List.getElem!_eq_getElem?_getD,same]

theorem saved_word (a : List Word) (i : Nat) (value : Word) (saved : a[i]?=some value) : a[i]! =value := by
  simp [List.getElem!_eq_getElem?_getD,saved]

/-- The row used by backward is exactly a view of the actual forward prefix. -/
theorem row_is_prefix (n : Nat) (forward : List Word) (size : n≤forward.length) :
    List.ofFn (SoftmaxStorage.row n forward)=forward.take n := by
  apply List.ext_getElem?; intro j
  by_cases inside : j<n
  · simp only [List.getElem?_ofFn,inside,dite_true,SoftmaxStorage.row,List.getElem?_take,ite_true]
    exact (SoftmaxStorage.some_bang forward j (lt_of_lt_of_le inside size)).symm
  · simp [List.getElem?_ofFn,inside,List.getElem?_take]

end Ptx.Scalar.Parallel.SoftmaxBackward
