import PoissonPTX.DotWitnessLayout

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
open Reduction.Control.Witness256

def compared (phase : Fin 8) (s : Flow.State) : Flow.State :=
  {Flow.next s with predicates:=Function.update s.predicates 0 (Flow.Compare.ge.apply (s.core.regs 14) (BitVec.ofNat 64 (stride phase)))}

def guarded (phase : Fin 8) (s : Flow.State) : Flow.State :=
  if (compared phase s).predicates 0=true then
    Flow.goto (compared phase s) (barrierSite ⟨phase.val+1,by omega⟩)
  else Flow.next (compared phase s)

theorem guarded_frame (frame : Frame base thread s.core) : Frame base thread (guarded phase s).core := by
  unfold guarded
  split <;> exact frame

theorem guarded_live : (guarded phase s).halted=s.halted := by unfold guarded; split <;> rfl

theorem guarded_pc {thread : Fin 256}
    (lane : (s.core.regs 14).toNat=thread.val) :
    (guarded phase s).core.pc=if thread.val<stride phase then s.core.pc+2 else barrierSite ⟨phase.val+1,by omega⟩ := by
  have fits : stride phase<2^32 := by have := (checked_read_layout phase false).2.2; omega
  have comparison := NativeGuard.compare_value lane (by decide +kernel) fits
  simp only [guarded,compared,Function.update_self,comparison,Flow.next,Flow.goto,advance]
  by_cases active : thread.val<stride phase <;> simp [active,show (stride phase≤thread.val) ↔ ¬thread.val<stride phase by omega]

/-- The witness executes the real comparison and branch as two instructions.
Its local result is computed from the actual lane register. -/
theorem guard_run (start : NativeFlow.State 256) (thread : Fin 256) (phase : Fin 8)
    (pc : (start.core.lanes thread).pc=24+9*phase.val)
    (fresh : start.core.barrier.arrived thread=false) (live : start.halted thread=false) :
    NativeFlow.Runs cfg ctx (program count left right output scratch) start [] []
      (NativeFlow.update start thread (guarded phase (NativeFlow.lane start thread))) := by
  let middle := NativeFlow.update start thread (compared phase (NativeFlow.lane start thread))
  have first : NativeFlow.Step cfg ctx (program count left right output scratch) thread start ⟨middle,[],[]⟩ := by
    apply NativeFlow.Step.flow (access:=none) (index:=none) live fresh
    · rw [pc]; exact compare_fetch phase
    · apply Flow.Observed.Eval.simple
      intro op same; cases same
  have nextPC : (middle.core.lanes thread).pc=25+9*phase.val := by
    simp [middle,NativeFlow.update,setLane,compared,Flow.next,NativeFlow.lane,advance,pc]; omega
  have second : NativeFlow.Step cfg ctx (program count left right output scratch) thread middle
      ⟨NativeFlow.update middle thread (guarded phase (NativeFlow.lane start thread)),[],[]⟩ := by
    apply NativeFlow.Step.flow (s:=middle) (access:=none) (index:=none)
      (by simp [middle,NativeFlow.update,compared,Flow.next,NativeFlow.lane,live]) (by exact fresh)
    · rw [nextPC]; exact branch_fetch phase
    · have same := NativeFlow.lane_update_self start thread (compared phase (NativeFlow.lane start thread))
      change NativeFlow.lane middle thread=compared phase (NativeFlow.lane start thread) at same
      rw [same]
      apply Flow.Observed.Eval.simple
      intro op equal; cases equal
  have joined := NativeFlow.Runs.cons first (NativeFlow.Runs.cons second NativeFlow.Runs.nil)
  simpa only [middle,NativeFlow.update_twice,List.nil_append] using joined

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
