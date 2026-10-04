import PoissonPTX.Initialize

namespace PtxTorchLean.Poisson.PTX.Initialize
set_option maxHeartbeats 200000
set_option maxRecDepth 10000

theorem masked_frame :
    (masked ctx s boundary input).core.global=s.core.global ∧
    (masked ctx s boundary input).core.globalStart=s.core.globalStart ∧
    (masked ctx s boundary input).core.globalBytes=s.core.globalBytes ∧
    (masked ctx s boundary input).core.regs 0=s.core.regs 0 ∧
    (masked ctx s boundary input).core.regs 12=s.core.regs 12 ∧
    (masked ctx s boundary input).halted=s.halted := by
  simp [masked,loadLoaded,maskLoaded,Assembly.maskLoaded,Flow.simple,Flow.next,assign,advance,addressed]
  split <;> simp

theorem copied_frame :
    (copied ctx s boundary input rhs r).core.globalStart=s.core.globalStart ∧
    (copied ctx s boundary input rhs r).core.globalBytes=s.core.globalBytes ∧
    (copied ctx s boundary input rhs r).core.regs 0=s.core.regs 0 ∧
    (copied ctx s boundary input rhs r).core.regs 12=s.core.regs 12 ∧
    (copied ctx s boundary input rhs r).halted=s.halted := by
  simp only [copied,StorePair.finish_frame.1,StorePair.finish_frame.2.1,
    StorePair.finish_frame.2.2.2.1,StorePair.finish_frame.2.2.2.2.1,
    masked_frame.2.1,masked_frame.2.2.1,masked_frame.2.2.2.1,
    masked_frame.2.2.2.2.1,masked_frame.2.2.2.2.2,and_self]

theorem ready_frame :
    (ready ctx s boundary input rhs r diagonal).core.global=(copied ctx s boundary input rhs r).core.global ∧
    (ready ctx s boundary input rhs r diagonal).core.globalStart=s.core.globalStart ∧
    (ready ctx s boundary input rhs r diagonal).core.globalBytes=s.core.globalBytes ∧
    (ready ctx s boundary input rhs r diagonal).core.regs 0=s.core.regs 0 ∧
    (ready ctx s boundary input rhs r diagonal).core.regs 12=s.core.regs 12 ∧
    (ready ctx s boundary input rhs r diagonal).halted=s.halted := by
  simp [ready,diagonalLoaded,Flow.simple,Flow.next,assign,advance,addressed,
    copied_frame.1,copied_frame.2.1,copied_frame.2.2.2.2]
  split <;> simp [copied_frame.2.2.1,copied_frame.2.2.2.1]

theorem ready_address : address (ready ctx s boundary input rhs r diagonal).core 12 field=address s.core 12 field := by
  simp only [address,wide,ready_frame.2.2.2.1,ready_frame.2.2.2.2.1]

theorem prefix_trace (running : s.halted=false) (valid : Valid s.core boundary input rhs r diagonal z p x) :
    Flow.Sequence ctx (prefixCode boundary input rhs r diagonal) s (ready ctx s boundary input rhs r diagonal) := by
  have mask := Flow.sequence_data (ctx:=ctx) (s:=s) (Indexed.run_sound (Assembly.mask_load_execution valid.2)) running
  have loadValid : Valid64 (maskLoaded s boundary).core.globalStart (maskLoaded s boundary).core.globalBytes
      (address (maskLoaded s boundary).core 12 input).toNat := by
    simpa [maskLoaded,Assembly.maskLoaded,assign,advance,address,wide] using valid.1 input (by simp)
  have loadRun := Flow.scalar_sequence (ctx:=ctx) (s:=maskLoaded s boundary) (run_sound (load_run _ 4 12 input loadValid)) running
  have select : Flow.Sequence ctx [.compare 0 .ne (.reg 21) (.imm 0),.select 0 true 4 (.imm 0)]
      (loadLoaded s boundary input) (masked ctx s boundary input) :=
    .cons running (.simple (by intro op h; cases h)) (.cons running (.simple (by intro op h; cases h)) .nil)
  have storeValid (field : Word) (member : field∈[input,rhs,r,diagonal,z,p,x]) :
      Valid64 (masked ctx s boundary input).core.globalStart (masked ctx s boundary input).core.globalBytes
        (address (masked ctx s boundary input).core 12 field).toNat := by
    simpa only [address,wide,masked_frame.2.1,masked_frame.2.2.1,masked_frame.2.2.2.1,
      masked_frame.2.2.2.2.1] using valid.1 field member
  have copies := Flow.scalar_sequence (ctx:=ctx) (s:=masked ctx s boundary input)
    (run_sound (StorePair.executes _ 4 rhs r (by decide) (by decide) (storeValid rhs (by simp)) (storeValid r (by simp))))
    (masked_frame.2.2.2.2.2.trans running)
  have diagonalValid : Valid64 (copied ctx s boundary input rhs r).core.globalStart (copied ctx s boundary input rhs r).core.globalBytes
      (address (copied ctx s boundary input rhs r).core 12 diagonal).toNat := by
    simpa only [address,wide,copied_frame.1,copied_frame.2.1,copied_frame.2.2.1,copied_frame.2.2.2.1] using valid.1 diagonal (by simp)
  have diag := Flow.scalar_sequence (ctx:=ctx) (s:=copied ctx s boundary input rhs r)
    (run_sound (load_run _ 5 12 diagonal diagonalValid)) (copied_frame.2.2.2.2.trans running)
  have lastRunning : (diagonalLoaded ctx s boundary input rhs r diagonal).halted=false := by
    change (copied ctx s boundary input rhs r).halted=false
    exact (copied_frame (ctx:=ctx) (s:=s) (boundary:=boundary) (input:=input) (rhs:=rhs) (r:=r)).2.2.2.2.trans running
  have last : Flow.Sequence ctx [.select 0 true 5 (.imm PreconditionUpdate.one)]
      (diagonalLoaded ctx s boundary input rhs r diagonal) (ready ctx s boundary input rhs r diagonal) :=
    .cons lastRunning (.simple (by intro op h; cases h)) .nil
  simpa only [prefixCode,List.append_assoc] using Flow.sequence_append mask
    (Flow.sequence_append loadRun (Flow.sequence_append select (Flow.sequence_append copies (Flow.sequence_append diag last))))

end PtxTorchLean.Poisson.PTX.Initialize
