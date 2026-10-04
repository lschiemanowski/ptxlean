import PoissonPTX.DotComplete
import PoissonPTX.DotPublication

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness

/-- Complete native execution and publication at the next launch boundary.
All source-admission and store evidence comes from the constructed history.
Publication order may vary without changing the decoded output or other bytes. -/
theorem complete_published (start : NativeFlow.State 256)
    (entry : ∀ thread, (start.core.lanes thread).pc=0) (live : ∀ thread, start.halted thread=false)
    (reset : start.core.barrier=Ptx.Barrier.reset generation) (noSite : start.core.site=none)
    (sameInitial : ∀ thread, (start.core.lanes thread).global=initial .global)
    (arena : ∀ thread, (ctx thread).arena=base)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (bounded : count<2^30)
    (arrays : ∀ thread, DotInput.Arrays (DotInput.setup (ctx thread) scratch (NativeFlow.lane start thread)).core count left right)
    (aligned : scratch.toNat%8=0)
    (shared : ∀ thread, (start.core.lanes thread).sharedStart=scratch.toNat ∧
      2048≤(start.core.lanes thread).sharedBytes ∧ scratch.toNat+(start.core.lanes thread).sharedBytes≤2^64)
    (outputs : ∀ thread, Valid64 (start.core.lanes thread).globalStart (start.core.lanes thread).globalBytes
      ((ctx thread).arena+output).toNat)
    (apart : OutputApart count left right output)
    (outputFits : base.toNat+output.toNat+8≤2^64) :
    ∃ final events indices source,
      NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final ∧
      (∀ t, final.halted t=true) ∧ Visibility.Compatible initial events source ∧
      Visibility.Repeated.OrderedSources events source ∧
      ∀ order, order.Perm events →
        decode (read64 (GlobalPublication.publish (initial .global) order) (base+output).toNat)=
          Binary64.reduce256 (Numeric.partialInputs ctx scratch start count left right) ∧
        ∀ p, p<(base+output).toNat ∨ (base+output).toNat+8≤p →
          GlobalPublication.publish (initial .global) order p=initial .global p := by
  obtain ⟨final,events,indices,source,access,run,returned,compatible,ordered,member,position,write,global,value⟩ :=
    complete (cfg:=cfg) start entry live reset noSite sameInitial arena laneMap bounded arrays aligned shared outputs apart outputFits
  have noWrap : scratch.toNat+2048≤2^64 := by have := (shared 0).2.1; have := (shared 0).2.2; omega
  refine ⟨final,events,indices,source,run,returned,compatible,ordered,?_⟩
  intro order permutation
  exact ⟨published_output run reset entry live arena laneMap sameInitial bounded apart arrays outputFits noWrap compatible ordered (returned 0) permutation,
    fun p outside => publication_outside run (by intro t h; simp [reset,Ptx.Barrier.reset] at h) entry arena permutation outside⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
