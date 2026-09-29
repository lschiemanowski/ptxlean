import PoissonPTX.ConcurrentReadOnly

/-! Connect the actual stored register, and a later published load, to the
ordered TorchLean contraction. The input snapshot still needs source evidence. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Replay

/-- Actual store preparation, excluding the store itself. -/
def storePrefix : List Op := [.wide8 1 (.reg 14),.add64 2 (.reg 3) (.reg 1)]

/-- Replay through address preparation, then inspect the actual store step.
Neither the store word nor a contraction answer is supplied as a premise. -/
theorem stored_contraction
    (run : Runs cfg program start events before) (aligned : Aligned start)
    (forward : Forward program) (pre suffix : List Op)
    (slice : Slice program (pre++(Contraction.program width acc a b++storePrefix)++suffix)
      pre.length (pre.length+(Contraction.program width acc a b++storePrefix).length))
    (pc : (start.lanes thread).pc=pre.length)
    (done : (before.lanes thread).pc=pre.length+(Contraction.program width acc a b++storePrefix).length)
    (reads : Reads memory thread pre.length
      (pre.length+(Contraction.program width acc a b++storePrefix).length) events)
    (allowed : Contraction.Accumulator acc)
    (valid : ∀ k<width, Contraction.Valid (view memory (start.lanes thread)) width k a ∧
      Contraction.Valid (view memory (start.lanes thread)) width k b)
    {address : Operand}
    (step : Step cfg program selected before out)
    (store : program[(before.lanes thread).pc]?=some (.data (.store64 .shared address (.reg acc))))
    (observed : Event.data thread access∈out.events) :
    access.data.store=true ∧ access.space=.shared ∧
    decode access.data.value=
      Spec.get2 (Spec.matMulSpec (Contraction.leftTensor (view memory (start.lanes thread)) width a)
        (Contraction.rightTensor (view memory (start.lanes thread)) width b)) 0 0 := by
  have projected := run_view run aligned slice forward (by omega) (by omega) reads
  have block := Contraction.fetched_block pre _ suffix projected pc done
  obtain ⟨middle,left,right⟩ := block_split _ _ block
  have result := (Contraction.correct allowed valid left).1
  have preserved := SharedStore.block_keeps right (r:=acc) (by
    rcases allowed with rfl | rfl <;> simp [storePrefix,SharedStore.keeps])
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin step observed
  subst selected
  rw [store] at fetch
  cases fetch
  cases hd with
  | store =>
    refine ⟨rfl,rfl,?_⟩
    change decode ((before.lanes thread).regs acc)=_
    change (before.lanes thread).regs acc=middle.regs acc at preserved
    rw [preserved,result,Contraction.tensor_fold]

/-- Numerical equality of the published load follows from a proved producer
answer and source-level publication. This lemma preserves their separate roles. -/
theorem published_contraction
    (compatible : Visibility.Compatible initial events source)
    (performed : Visibility.Performed events source)
    (hw : events[w]?=some (Event.data writer wa))
    (hr : events[r]?=some (Event.data reader ra))
    (write : wa.data.store=true) (read : ra.data.store=false)
    (sw : wa.space=.shared) (sr : ra.space=.shared)
    (same : wa.data.address=ra.data.address) (ordered : Visibility.Across events w r)
    (owner : Visibility.SoleWriter events w ra.data.address)
    (computed : decode wa.data.value=answer) : decode ra.data.value=answer := by
  rw [(Visibility.read_from_writer compatible performed hw hr write read sw sr same ordered owner).1]
  exact computed

end PtxTorchLean.Poisson.PTX.Concurrent.Replay
