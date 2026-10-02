import PoissonPTX.AssemblyObservedOffsets
import PoissonPTX.ObservedAccessShape

namespace PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
set_option maxHeartbeats 1000000
variable {next : Bool}

/-- Both offset reads have launch-derived addresses, before either loaded
integer has been justified by the memory source constraints. -/
theorem offset_address (step : Flow.Observed.Step ctx
    (entryCode count offsets entries element mask boundary output) s t access (some a))
    (ready : OffsetsReady ctx offsets s) (which : a.pc=(if next then 14 else 9)) :
    a.address=(address32 ctx.arena (if next then Kernel.u32 (nextWord ctx) else Kernel.Residual.index ctx) offsets).toNat := by
  obtain ⟨_,op,fetch,execution⟩ := step
  obtain ⟨dst,addr,opEq,pcEq,addressEq⟩ := Flow.Observed.index_shape execution
  subst op
  have pc : s.core.pc=(if next then 14 else 9) := pcEq.symm.trans which
  cases next <;>
    simp only [entryCode,Flow.Window.program,entryPrefix,prologue,prepareCode,Flow.Window.header,
      pc,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      List.getElem?_cons_zero,List.getElem?_cons_succ,ite_true,ite_false,Bool.false_eq_true] at fetch
  all_goals simp at fetch
  all_goals rcases fetch with ⟨rfl,rfl⟩
  all_goals rw [addressEq]
  · simp only [OffsetsReady] at ready
    rw [ready.2.2.1 (by simpa using pc)]
    rfl
  · simp only [OffsetsReady] at ready
    rw [ready.2.2.2.2.2.2 (by simpa using pc)]
    rfl

theorem offset_records (run : Flow.Observed.Runs ctx
    (entryCode count offsets entries element mask boundary output) s words indices t)
    (launch : Ready ctx mask output s) (ready : OffsetsReady ctx offsets s)
    (member : a∈indices) (which : a.pc=(if next then 14 else 9)) :
    a.address=(address32 ctx.arena (if next then Kernel.u32 (nextWord ctx) else Kernel.Residual.index ctx) offsets).toNat := by
  induction run with
  | nil => simp at member
  | @cons s middle access indexRecord words indices t step rest ih =>
    rcases List.mem_append.mp member with first | later
    · have observed : indexRecord=some a := by simpa using first
      exact offset_address (observed ▸ step) ready which
    · exact ih (step_ready step launch) (offsets_step step launch ready) later

end PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress
