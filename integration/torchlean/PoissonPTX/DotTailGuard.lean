import PoissonPTX.DotTailBody

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail

def compared (s : Flow.State) : Flow.State :=
  {Flow.next s with predicates:=Function.update s.predicates 0 (Flow.Compare.ne.apply (s.core.regs 14) 0)}

def guarded (s : Flow.State) : Flow.State :=
  if (compared s).predicates 0=true then Flow.halt (compared s) else Flow.next (compared s)

theorem guard_pc : (guarded s).core.pc=s.core.pc+2 := by
  unfold guarded; split <;> rfl

theorem guard_core : (guarded s).core={s.core with pc:=s.core.pc+2} := by
  unfold guarded; split <;> rfl

theorem comparison {thread : Fin 256} (lane : (s.core.regs 14).toNat=thread.val) :
    (compared s).predicates 0=decide (thread.val≠0) := by
  have low : thread.val<4294967296 := by have := thread.isLt; omega
  have value : (Kernel.u32 (s.core.regs 14)).toNat=thread.val := by
    simp [Kernel.u32,BitVec.toNat_setWidth,lane,Nat.mod_eq_of_lt low]
  have zero : Kernel.u32 (s.core.regs 14)=0 ↔ thread.val=0 := by
    constructor
    · intro h; have eq := congrArg BitVec.toNat h; simpa [value] using eq
    · intro h; apply BitVec.eq_of_toNat_eq; simp [value,h]
  simp only [compared,Function.update_self,Flow.Compare.apply]
  change (Kernel.u32 (s.core.regs 14) != 0)=decide (thread.val≠0)
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne,decide_eq_true_eq,ne_eq,zero]

theorem guard_halted {thread : Fin 256} (lane : (s.core.regs 14).toNat=thread.val)
    (live : s.halted=false) : (guarded s).halted=decide (thread.val≠0) := by
  unfold guarded
  rw [comparison lane]
  by_cases zero : thread.val=0 <;> simp [zero,Flow.halt,compared,Flow.next,live]

/-- The final lane selection is the actual unsigned comparison and predicated
return. Nonzero lanes really halt here; lane zero proceeds to its output store. -/
theorem guard_run (start : NativeFlow.State 256) (thread : Fin 256)
    (pc : (start.core.lanes thread).pc=96)
    (fresh : start.core.barrier.arrived thread=false) (live : start.halted thread=false) :
    NativeFlow.Runs cfg ctx (program count left right output scratch) start [] []
      (NativeFlow.update start thread (guarded (NativeFlow.lane start thread))) := by
  let middle := NativeFlow.update start thread (compared (NativeFlow.lane start thread))
  have first : NativeFlow.Step cfg ctx (program count left right output scratch) thread start ⟨middle,[],[]⟩ := by
    apply NativeFlow.Step.flow (access:=none) (index:=none) live fresh
    · rw [pc,show 96=96+0 by rfl,tail_fetch]; rfl
    · apply Flow.Observed.Eval.simple
      intro op same; cases same
  have nextPC : (middle.core.lanes thread).pc=97 := by
    simp [middle,NativeFlow.update,setLane,compared,Flow.next,NativeFlow.lane,advance,pc]
  have second : NativeFlow.Step cfg ctx (program count left right output scratch) thread middle
      ⟨NativeFlow.update middle thread (guarded (NativeFlow.lane start thread)),[],[]⟩ := by
    apply NativeFlow.Step.flow (s:=middle) (access:=none) (index:=none)
      (by simp [middle,NativeFlow.update,compared,Flow.next,NativeFlow.lane,live]) (by exact fresh)
    · rw [nextPC,show 97=96+1 by rfl,tail_fetch]; rfl
    · have same := NativeFlow.lane_update_self start thread (compared (NativeFlow.lane start thread))
      change NativeFlow.lane middle thread=compared (NativeFlow.lane start thread) at same
      rw [same]
      apply Flow.Observed.Eval.simple
      intro op equal; cases equal
  have joined := NativeFlow.Runs.cons first (NativeFlow.Runs.cons second NativeFlow.Runs.nil)
  simpa only [middle,NativeFlow.update_twice,List.nil_append] using joined

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail
