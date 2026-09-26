import PtxBinary32.GridPointwiseLaunch

/-! A logical vector can end partway through a physical group. Extra lanes have
explicit valid input pointers and their own allocated padding outputs. Only the
logical nonemptyPrefix is exported; padded words are not claimed to remain unchanged. -/
namespace Ptx.Scalar.Parallel.GridPointwise

def groupCount (count width : Nat) : Nat := (count+width-1)/width

theorem capacity_bounds (count width : Nat) (positive : 0<width) :
    count≤groupCount count width*width ∧ groupCount count width*width<count+width := by
  have decomposition := Nat.mod_add_div (count+width-1) width
  have remainder := Nat.mod_lt (count+width-1) positive
  unfold groupCount
  rw [Nat.mul_comm width] at decomposition
  omega

theorem empty_groupCount (width : Nat) (positive : 0<width) : groupCount 0 width=0 := by
  unfold groupCount
  exact Nat.div_eq_of_lt (by omega)

/-- Padding lanes read source word zero, whose allocation is explicitly required.
The logical source mapping is unchanged, and every output address is distinct. -/
def paddedLayout (l : Pointwise.Layout count) (width : Nat) (positive : 0<width)
    (nonemptyPrefix : 0<l.prefixWords) (small : l.prefixWords+groupCount count width*width<2^30) :
    Layout (groupCount count width) width where
  prefixWords := l.prefixWords
  left := fun t => if h : t.val<count then l.left ⟨t.val,h⟩ else 0
  right := fun t => if h : t.val<count then l.right ⟨t.val,h⟩ else 0
  leftBound := by intro t; split <;> first | exact l.leftBound _ | exact nonemptyPrefix
  rightBound := by intro t; split <;> first | exact l.rightBound _ | exact nonemptyPrefix
  small := small

/-- General input words are allowed, including zeros, infinities and NaNs under
the same pointwise instruction contracts. No numerical precondition is needed. -/
theorem padded_exists (op : Pointwise.Op) (l : Pointwise.Layout count) (width : Nat)
    (positive : 0<width) (resource : width≤1024) (nonemptyPrefix : 0<l.prefixWords)
    (small : l.prefixWords+groupCount count width*width<2^30) (before : List Word)
    (storage : l.prefixWords+groupCount count width*width≤before.length) :
    ∃ after, Launch op (paddedLayout l width positive nonemptyPrefix small) before after :=
  launch_exists op _ before positive resource storage

/-- Correct logical outputs, read-only source preservation and physical extent
preservation all follow from the actual admitted grid launch. -/
theorem padded_correct (op : Pointwise.Op) (l : Pointwise.Layout count) (width : Nat)
    (positive : 0<width) (nonemptyPrefix : 0<l.prefixWords)
    (small : l.prefixWords+groupCount count width*width<2^30) (before after : List Word)
    (run : Launch op (paddedLayout l width positive nonemptyPrefix small) before after) :
    (∀ t : Fin count, ∃ value, after[l.output t]?=some value ∧
      Pointwise.Result op before[l.left t]! before[l.right t]! value) ∧
    (∀ i, i<l.prefixWords → after[i]?=before[i]?) ∧ after.length=before.length := by
  have result := launch_correct run
  refine ⟨?_,result.2⟩
  intro t
  let u : Fin (groupCount count width*width) := ⟨t.val,lt_of_lt_of_le t.isLt (capacity_bounds count width positive).1⟩
  simpa [paddedLayout,u,Pointwise.Layout.output,t.isLt] using result.1 u

end Ptx.Scalar.Parallel.GridPointwise
