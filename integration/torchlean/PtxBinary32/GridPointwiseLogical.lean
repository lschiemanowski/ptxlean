import PtxBinary32.GridPointwisePadding

/-! A logical vector view of a padded pointwise launch. The host model appends
explicit spare output storage and returns its original-length prefix. Padding
writes are retained in the actual launch, never presented as preserved cells. -/
namespace Ptx.Scalar.Parallel.GridPointwise

def extend (l : Pointwise.Layout count) (width : Nat) (before : List Word) : List Word :=
  before++List.replicate (groupCount count width*width-count) 0

inductive LogicalLaunch (op : Pointwise.Op) (l : Pointwise.Layout count) (before : List Word) : List Word → Prop
  | empty (zero : count=0) : LogicalLaunch op l before before
  | kernel (width : Nat) (positive : 0<width) (nonemptyPrefix : 0<l.prefixWords)
      (small : l.prefixWords+groupCount count width*width<2^30)
      (size : before.length=l.prefixWords+count) {physical : List Word}
      (run : Launch op (paddedLayout l width positive nonemptyPrefix small) (extend l width before) physical) :
      LogicalLaunch op l before (physical.take before.length)

theorem logical_exists (op : Pointwise.Op) (l : Pointwise.Layout count) (before : List Word)
    (margin : l.prefixWords+count+32<2^30) (size : before.length=l.prefixWords+count) :
    ∃ after, LogicalLaunch op l before after := by
  by_cases zero : count=0
  · exact ⟨before,.empty zero⟩
  · have positive : 0<32 := by decide
    have nonemptyPrefix : 0<l.prefixWords := by
      have bound := l.leftBound ⟨0,by omega⟩; omega
    have capacity := capacity_bounds count 32 positive
    have small : l.prefixWords+groupCount count 32*32<2^30 := by omega
    obtain ⟨physical,run⟩ := padded_exists op l 32 positive (by decide) nonemptyPrefix small (extend l 32 before)
      (by simp only [extend,List.length_append,List.length_replicate,size]; omega)
    exact ⟨_,.kernel 32 positive nonemptyPrefix small size run⟩

theorem logical_correct (run : LogicalLaunch op l before after) :
    (∀ t, ∃ value, after[l.output t]?=some value ∧ Pointwise.Result op before[l.left t]! before[l.right t]! value) ∧
    (∀ i, i<l.prefixWords → after[i]?=before[i]?) ∧ after.length=before.length := by
  cases run with
  | empty zero => exact ⟨by intro t; have := t.isLt; omega,fun _ _ => rfl,rfl⟩
  | kernel width positive nonemptyPrefix small size run =>
    have result := padded_correct _ _ _ positive nonemptyPrefix small _ _ run
    refine ⟨?_,?_,?_⟩
    · intro t
      obtain ⟨value,saved,correct⟩ := result.1 t
      have outputBound : l.output t<before.length := by have := t.isLt; unfold Pointwise.Layout.output; omega
      have leftBound : l.left t<before.length := by have := l.leftBound t; omega
      have rightBound : l.right t<before.length := by have := l.rightBound t; omega
      refine ⟨value,by simpa [List.getElem?_take,outputBound] using saved,?_⟩
      simpa [extend,List.getElem!_eq_getElem?_getD,List.getElem?_append_left leftBound,
        List.getElem?_append_left rightBound] using correct
    · intro i hi
      have bound : i<before.length := by omega
      simpa [extend,List.getElem?_take,bound,List.getElem?_append_left bound] using result.2.1 i hi
    · rw [List.length_take,result.2.2]
      simp [extend]
end Ptx.Scalar.Parallel.GridPointwise
