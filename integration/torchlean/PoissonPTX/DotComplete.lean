import PoissonPTX.DotWitnessAdmission
import PoissonPTX.DotOutputExists
import PoissonPTX.DotOutputValue

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness

/-- From valid launch data, construct a complete source-admitted native dot
execution with a real output store and prove its decoded numerical value.
The witness chooses a finite schedule; it is not a universal GPU-progress or
full PTX-memory-admission theorem. -/
theorem complete (start : NativeFlow.State 256)
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
    ∃ final events indices source access,
      NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final ∧
      (∀ t, final.halted t=true) ∧ Visibility.Compatible initial events source ∧
      Visibility.Repeated.OrderedSources events source ∧ Event.data 0 access∈events ∧
      access.data.pc=102 ∧ access.data.store=true ∧ access.space=.global ∧
      decode access.data.value=Binary64.reduce256 (Numeric.partialInputs ctx scratch start count left right) := by
  obtain ⟨final,events,indices,input,run,returned,zeroPC,expected⟩ :=
    complete_candidate (cfg:=cfg) start entry live reset noSite sameInitial laneMap bounded arrays aligned shared outputs
  have noWrap : scratch.toNat+2048≤2^64 := by
    have := (shared 0).2.1
    have := (shared 0).2.2
    omega
  obtain ⟨source,compatible,ordered⟩ := admitted run reset entry laneMap noWrap expected
  obtain ⟨access,member,position,write,global⟩ := output_exists run reset (entry 0) zeroPC
  obtain ⟨w,found⟩ := List.mem_iff_getElem?.mp member
  exact ⟨final,events,indices,source,access,run,returned,compatible,ordered,member,position,write,global,
    Numeric.output_value run reset entry live arena laneMap sameInitial bounded apart arrays outputFits noWrap compatible ordered found write global⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
