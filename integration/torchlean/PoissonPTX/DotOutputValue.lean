import PoissonPTX.DotFinalRead
import PoissonPTX.DotStores

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric

variable {cfg : Config 256} {ctx : Fin 256 → Kernel.Context}
  {start final : NativeFlow.State 256} {events : List (Event 256)} {w : Nat}
  {thread : Fin 256} {access : Access}

def outputLoads (answer : Float) (pc : Nat) : Option (Fin 256 → Float) :=
  if pc=98 then some (fun _ => answer) else none

theorem output_tag : NativeFlow.Numeric.tag (program count left right output scratch) (outputLoads answer) 102 8=
    some (fun _ => answer) := rfl

/-- The actual global store uses the value loaded from shared memory four
instructions earlier, preserved through the output-address preparation. -/
theorem stored_output
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (reads : Values.Reads (outputLoads answer) events)
    (observed : events[w]?=some (.data thread access)) (atSite : access.data.pc=102) :
    decode access.data.value=answer := by
  obtain ⟨before,earlier,earlierIndices,selected,out,suffix,suffixIndices,j,hp,hs,hm,ht,he,hi⟩ := NativeFlow.event_prefix run observed
  obtain ⟨same,i,next,index,fetch,effect⟩ := NativeFlow.step_access_origin hs (List.mem_of_getElem? hm)
  subst selected
  have pc := (NativeFlow.eval_access_pc effect).1.symm.trans atSite
  change (before.core.lanes thread).pc=102 at pc
  have inv : NativeFlow.Numeric.Invariant (program count left right output scratch) (outputLoads answer) start := by
    intro t; rw [entry]; exact Values.empty_ready
  have ready := NativeFlow.Numeric.runs_invariant hp aligned inv entries
    (fun t a member => reads t a (by rw [he]; exact List.mem_append_left _ (List.mem_append_left _ member))) thread
  rw [pc] at ready
  have value := ready 8 (fun _ => answer) output_tag
  rw [pc] at fetch
  rw [show 102=96+6 by decide,tail_fetch] at fetch
  change some (NativeFlow.Instr.flow (.data (.data (.store64 .global (.reg 2) (.reg 8)))))=some (.flow i) at fetch
  cases fetch
  cases effect with
  | data step => cases step with
    | data step => cases step with
      | store valid => exact value

/-- Complete native dot-output correspondence, conditional on an actual
source-admitted execution. It derives the input traversal, all tree reads and
rounded additions, final shared read, and the actual global store operand. -/
theorem output_value
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ thread, (start.core.lanes thread).pc=0) (live : ∀ thread, start.halted thread=false)
    (arena : ∀ thread, (ctx thread).arena=base) (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (sameInitial : ∀ thread, (start.core.lanes thread).global=initial .global)
    (bounded : count<2^30) (apart : OutputApart count left right output)
    (arrays : ∀ thread, DotInput.Arrays (DotInput.setup (ctx thread) scratch (NativeFlow.lane start thread)).core count left right)
    (outputFits : base.toNat+output.toNat+8≤2^64) (noWrap : scratch.toNat+2048≤2^64)
    (compatible : Visibility.Compatible initial events source) (ordered : Visibility.Repeated.OrderedSources events source)
    (observed : events[w]?=some (.data thread access)) (write : access.data.store=true) (global : access.space=.global) :
    decode access.data.value=Binary64.reduce256 (partialInputs ctx scratch start count left right) := by
  have aligned : Aligned start.core := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  have atSite : access.data.pc=102 := by
    obtain ⟨before,earlier,earlierIndices,selected,out,prior,step,member⟩ := NativeFlow.access_prefix run (List.mem_of_getElem? observed)
    obtain ⟨same,i,next,index,fetch,effect⟩ := NativeFlow.step_access_origin step member
    obtain ⟨sp,addr,src,op,shape⟩ := Flow.Observed.store_shape effect write
    have spaceEq : sp=.global := by simpa only [shape] using global
    subst sp; subst i
    have position := (global_store_site fetch).1
    simpa only [shape,NativeFlow.lane] using position
  apply stored_output run aligned entry ?_ observed atSite
  intro reader ra member read f known
  unfold outputLoads at known
  split at known
  · rename_i atRead
    cases known
    obtain ⟨r,found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨v,wa,published,pc,write,shared,across,value,bytes⟩ :=
      final_read_source run reset entry laneMap noWrap compatible ordered found atRead
    rw [value]
    exact publication_value run reset entry live arena laneMap sameInitial bounded apart arrays outputFits noWrap compatible ordered 8 published pc
  · cases known

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric
