import PoissonPTX.DecodedPublication
import PoissonPTX.DotOutputValue
import PoissonPTX.DotZeroReturn

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- Publishing actual global stores preserves every byte outside the single
output word, including input arrays and unrelated solver state. -/
theorem publication_outside
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ owner, (start.core.lanes owner).pc=0)
    (arena : ∀ owner, (ctx owner).arena=base)
    (permutation : order.Perm events)
    (outside : p<(base+output).toNat ∨ (base+output).toNat+8≤p) :
    GlobalPublication.publish memory order p=memory p := by
  apply GlobalPublication.outside
  intro owner access member global write
  have address := (stores_output run aligned entry (permutation.mem_iff.mp member) write global).2
  rw [arena] at address
  simpa only [address] using outside

/-- A completed lane-zero execution supplies an actual store. Merging the
actual records in any order recovers its numerical output without fixing an
exceptional encoding or assuming the value in initial storage. This is a
mathematical launch-publication boundary, not a CUDA visibility theorem. -/
theorem published_output {cfg : Config 256} {ctx : Fin 256 → Kernel.Context}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ thread, (start.core.lanes thread).pc=0) (live : ∀ thread, start.halted thread=false)
    (arena : ∀ thread, (ctx thread).arena=base) (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (sameInitial : ∀ thread, (start.core.lanes thread).global=initial .global)
    (bounded : count<2^30) (apart : OutputApart count left right output)
    (arrays : ∀ thread, DotInput.Arrays (DotInput.setup (ctx thread) scratch (NativeFlow.lane start thread)).core count left right)
    (outputFits : base.toNat+output.toNat+8≤2^64) (noWrap : scratch.toNat+2048≤2^64)
    (compatible : Visibility.Compatible initial events source) (ordered : Visibility.Repeated.OrderedSources events source)
    (returned : final.halted 0=true) (permutation : order.Perm events) :
    decode (read64 (GlobalPublication.publish (initial .global) order) (base+output).toNat)=
      Binary64.reduce256 (Numeric.partialInputs ctx scratch start count left right) := by
  have aligned : Aligned start.core := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  apply GlobalPublication.numeric_permuted permutation
  · intro owner access member global write
    obtain ⟨w,found⟩ := List.mem_iff_getElem?.mp member
    have address := (stores_output run aligned entry member write global).2
    rw [arena] at address
    exact Or.inl ⟨address,Numeric.output_value run reset entry live arena laneMap sameInitial bounded apart arrays
      outputFits noWrap compatible ordered found write global⟩
  · have zero : (ctx 0).lane=0 := by apply BitVec.eq_of_toNat_eq; exact laneMap 0
    obtain ⟨access,member,position,write,global⟩ := zero_returned_store run reset entry (live 0) zero returned
    have address := (stores_output run aligned entry member write global).2
    rw [arena] at address
    exact ⟨0,access,member,global,write,address⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
