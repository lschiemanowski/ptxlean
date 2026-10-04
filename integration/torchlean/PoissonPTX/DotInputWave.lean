import PoissonPTX.DotInputRecorded
import PoissonPTX.NativeFlowSerial

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- Exact initialized reads from the input prefix; barriers and stores do not
belong to this trace segment. -/
def InputEvent (memory : Memory) : Event n → Prop
  | .data _ access => access.data.store=false ∧ access.space=.global ∧
      access.data.value=read64 memory access.data.address
  | .barrier _ => False

/-- A chosen finite schedule completes every actual lane input loop, preserving
its computed accumulator and frame. It introduces no extra barrier instruction. -/
theorem input_wave (start : NativeFlow.State n)
    (entry : ∀ thread, (start.core.lanes thread).pc=0) (live : ∀ thread, start.halted thread=false)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (sameInitial : ∀ thread, (start.core.lanes thread).global=memory)
    (bounded : count<2^30)
    (arrays : ∀ thread, DotInput.Arrays (DotInput.setup (ctx thread) scratch (NativeFlow.lane start thread)).core count left right) :
    ∃ final events indices, NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final ∧
      final.core.barrier=start.core.barrier ∧ final.core.site=start.core.site ∧
      (∀ thread, (final.core.lanes thread).pc=20 ∧ final.halted thread=false ∧
        decode ((final.core.lanes thread).regs 8)=DotInput.partialSum (ctx thread) scratch (NativeFlow.lane start thread) count left right ∧
        DotInput.Stable (DotInput.setup (ctx thread) scratch (NativeFlow.lane start thread)).core (final.core.lanes thread)) ∧
      ∀ e∈events, InputEvent memory e := by
  classical
  have each := fun thread => DotInput.input_exists (ctx thread) scratch (NativeFlow.lane start thread)
    (entry thread) (live thread) bounded (arrays thread)
  choose target scalar done running value frame using each
  obtain ⟨events,indices,run,good⟩ := NativeFlow.Serial.run_lanes start target (InputEvent memory)
    (fun thread state same barrierEq siteEq => by
      obtain ⟨words,localIndices,observed,globalFrame,wordValues⟩ := input_recorded (scalar thread)
      have fullFetch : ∀ (pc : Nat) (i : Flow.Instr), (DotInput.inputProgram count left right scratch)[pc]?=some i →
          (program count left right output scratch)[pc]?=some (.flow i) := by
        intro pc i fetch
        have bound := (List.getElem?_eq_some_iff.mp fetch).1
        rw [DotInput.input_length] at bound
        rw [input_fetch bound,fetch]
        rfl
      have lifted := NativeFlow.lift_local (cfg:=cfg) (ctx:=ctx) (start:=state)
        (same ▸ observed) (by rw [barrierEq,reset]; rfl) fullFetch
      refine ⟨words.map (Event.data thread),localIndices.map (thread,·),lifted,?_⟩
      intro e member
      obtain ⟨a,found,rfl⟩ := List.mem_map.mp member
      obtain ⟨read,space,word⟩ := wordValues a found
      exact ⟨read,space,by simpa only [NativeFlow.lane,sameInitial] using word⟩)
  refine ⟨NativeFlow.Serial.allLanes start target,events,indices,run,rfl,rfl,?_,good⟩
  intro thread
  exact ⟨done thread,running thread,value thread,frame thread⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
