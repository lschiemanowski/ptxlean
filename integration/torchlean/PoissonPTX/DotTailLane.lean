import PoissonPTX.DotTailGuard

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail

def target (s : Flow.State) (output word : Word) (thread : Fin 256) : Flow.State :=
  if thread.val=0 then Flow.halt {guarded s with core:=finish (guarded s).core output word}
  else guarded s

def records (s : Flow.State) (output word : Word) (thread : Fin 256) : List Access :=
  if thread.val=0 then events (guarded s).core output word else []

theorem target_halted (lane : (s.core.regs 14).toNat=thread.val) (live : s.halted=false) :
    (target s output word thread).halted=true := by
  unfold target
  split
  · rfl
  · rw [guard_halted lane live]; simp_all

/-- Execute one lane's complete epilogue, keeping the exact final shared read
and output store for lane zero, and no memory records for the other lanes. -/
theorem lane_run (start : NativeFlow.State 256) (thread : Fin 256)
    (pc : (start.core.lanes thread).pc=96)
    (lane : ((start.core.lanes thread).regs 14).toNat=thread.val)
    (fresh : start.core.barrier.arrived thread=false) (live : start.halted thread=false)
    (shared : Valid64 (start.core.lanes thread).sharedStart (start.core.lanes thread).sharedBytes ((start.core.lanes thread).regs 3).toNat)
    (global : Valid64 (start.core.lanes thread).globalStart (start.core.lanes thread).globalBytes ((start.core.lanes thread).regs 0+output).toNat) :
    NativeFlow.Runs cfg ctx (program count left right output scratch) start
      ((records (NativeFlow.lane start thread) output word thread).map (Event.data thread)) []
      (NativeFlow.update start thread (target (NativeFlow.lane start thread) output word thread)) := by
  have guard := guard_run (cfg:=cfg) (ctx:=ctx) (count:=count) (left:=left) (right:=right) (output:=output) (scratch:=scratch) start thread pc fresh live
  by_cases zero : thread.val=0
  · let middle := NativeFlow.update start thread (guarded (NativeFlow.lane start thread))
    have middlePC : (middle.core.lanes thread).pc=98 := by
      simp only [middle,NativeFlow.update,setLane,Function.update_self,guard_pc,NativeFlow.lane,pc]
    have middleLive : middle.halted thread=false := by
      simp only [middle,NativeFlow.update,Function.update_self]
      rw [guard_halted lane live]; simp [zero]
    have body := block (middle.core.lanes thread) output word
      (by simpa only [middle,NativeFlow.update,setLane,Function.update_self,guard_core,NativeFlow.lane] using shared)
      (by simpa only [middle,NativeFlow.update,setLane,Function.update_self,guard_core,NativeFlow.lane] using global)
    have fetch : ∀ (j : Nat) (op : Op), (code output)[j]?=some op →
        (program count left right output scratch)[(middle.core.lanes thread).pc+j]?=some (.flow (.data (.data op))) := by
      intro j op found
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simpa only [middlePC,found,Option.map_some] using
        (body_fetch (count:=count) (left:=left) (right:=right) (scratch:=scratch) (output:=output) ⟨j,by simpa [code] using bound⟩)
    have bodyRun := NativeFlow.lift_block (cfg:=cfg) (ctx:=ctx) body (by exact fresh) middleLive fetch
    let after := NativeFlow.update middle thread {NativeFlow.lane middle thread with core:=finish (middle.core.lanes thread) output word}
    have afterPC : (after.core.lanes thread).pc=103 := by
      simp [after,NativeFlow.update,setLane,finish,prepared,put,assign,advance,middlePC]
    have last : NativeFlow.Step cfg ctx (program count left right output scratch) thread after
        ⟨NativeFlow.update after thread (Flow.halt (NativeFlow.lane after thread)),[],[]⟩ := by
      apply NativeFlow.Step.flow (access:=none) (index:=none)
        (by simp [after,NativeFlow.update,NativeFlow.lane,middleLive]) (by exact fresh)
      · rw [afterPC,show 103=96+7 by rfl,tail_fetch]; rfl
      · apply Flow.Observed.Eval.simple; intro op eq; cases eq
    have joined := NativeFlow.append guard (NativeFlow.append bodyRun (NativeFlow.Runs.cons last NativeFlow.Runs.nil))
    simpa [records,target,zero,after,middle,NativeFlow.lane_update_self,NativeFlow.update_twice,
      NativeFlow.update,setLane,NativeFlow.lane] using joined
  · simpa [records,target,zero] using guard

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail
