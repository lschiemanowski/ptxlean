import PoissonPTX.UpdateXRZState
import PoissonPTX.UpdateXRZNumeric

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ

/-- The complete mixed body computes the three initial-input formulas with
separate binary64 operations. Its stores cannot corrupt later operands. -/
theorem correct (actual : Flow.Sequence ctx (body alpha p x ap r diagonal boundary z) s final)
    (running : s.halted=false) (valid : Valid s.core alpha p x ap r diagonal boundary z)
    (separated : Separate s.core x ap r diagonal boundary z) :
    decode (read64 final.core.global (address s.core 12 x).toNat)=xValue s.core alpha p x ∧
    decode (read64 final.core.global (address s.core 12 r).toNat)=rValue s.core alpha ap r ∧
    decode (read64 final.core.global (address s.core 12 z).toNat)=zValue s.core alpha ap r diagonal boundary ∧
    (∀ byte, (∀ field∈[x,r,z], byte<(address s.core 12 field).toNat ∨ (address s.core 12 field).toNat+8≤byte) →
      final.core.global byte=s.core.global byte) := by
  obtain ⟨xm,xv,rm,rv,zv,state,_,xEq,_,rEq,zEq⟩ := state_result actual running valid
  subst final
  have values := stored_words (ctx:=ctx) (alpha:=alpha) (p:=p) (xm:=xm) (xv:=xv) (rm:=rm) (rv:=rv) (zv:=zv) separated
  have rResult := rEq.trans (r_value separated)
  refine ⟨(congrArg decode values.1).trans (xEq.trans x_value),
    (congrArg decode values.2.1).trans rResult,
    (congrArg decode values.2.2).trans (zEq.trans (z_value separated rResult)),?_⟩
  intro byte outside
  rw [finish_global,write64_outside _ _ _ _ (outside z (by simp)),
    write64_outside _ _ _ _ (outside r (by simp)),write64_outside _ _ _ _ (outside x (by simp))]

/-- Fetch the real prologue, all 47 body instructions, and the return. -/
theorem entry_correct (actual : Flow.Runs ctx (entry count alpha p x ap r diagonal boundary z) s final)
    (pc : s.core.pc=0) (running : s.halted=false) (done : final.halted=true)
    (live : Kernel.Residual.live ctx count)
    (valid : Valid (Assembly.setup ctx count s).core alpha p x ap r diagonal boundary z)
    (separated : Separate (Assembly.setup ctx count s).core x ap r diagonal boundary z) :
    decode (read64 final.core.global (address (Assembly.setup ctx count s).core 12 x).toNat)=xValue (Assembly.setup ctx count s).core alpha p x ∧
    decode (read64 final.core.global (address (Assembly.setup ctx count s).core 12 r).toNat)=rValue (Assembly.setup ctx count s).core alpha ap r ∧
    decode (read64 final.core.global (address (Assembly.setup ctx count s).core 12 z).toNat)=zValue (Assembly.setup ctx count s).core alpha ap r diagonal boundary ∧
    (∀ byte, (∀ field∈[x,r,z], byte<(address (Assembly.setup ctx count s).core 12 field).toNat ∨
      (address (Assembly.setup ctx count s).core 12 field).toNat+8≤byte) → final.core.global byte=s.core.global byte) := by
  obtain ⟨middle,bodyRun,eq⟩ := VectorFlowEntry.completed_body actual pc running done live body_segment
  subst final
  have answer := correct bodyRun (Assembly.setup_active (s:=s) live) valid separated
  exact answer

end PtxTorchLean.Poisson.PTX.UpdateXRZ
