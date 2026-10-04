import PoissonPTX.UpdateXRZCorrect

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ

/-- Every valid local layout admits the actual update body, including NaNs,
infinities and zero diagonals. Numerical acceptance is a separate property. -/
theorem body_exists (s : Flow.State) (running : s.halted=false)
    (valid : Valid s.core alpha p x ap r diagonal boundary z) :
    ∃ final, Flow.Sequence ctx (body alpha p x ap r diagonal boundary z) s final ∧ final.halted=false := by
  let c := coefficient s alpha
  let xm := encode (RegisterUpdate.product c.core p)
  let xv := encode (RegisterUpdate.result .add c.core p x)
  let xs := solution s alpha p x xm xv
  let rm := encode (RegisterUpdate.product xs.core ap)
  let rv := encode (RegisterUpdate.result .sub xs.core ap r)
  let rs := residual s alpha p x ap r xm xv rm rv
  have vc : Valid c.core alpha p x ap r diagonal boundary z := coefficient_geometry.valid valid
  have vx : Valid xs.core alpha p x ap r diagonal boundary z := solution_geometry.valid valid
  have vr : Valid rs.core alpha p x ap r diagonal boundary z := residual_geometry.valid valid
  have first := Flow.scalar_sequence (ctx:=ctx) (s:=s) (run_sound (ScalarLoad.executes s.core 4 alpha valid.1)) running
  have second := Flow.scalar_sequence (ctx:=ctx) (s:=c) (RegisterUpdate.executes c.core .add p x x
    (vc.2.1 p (by simp)) (vc.2.1 x (by simp)) (vc.2.1 x (by simp))) running
  have third := Flow.scalar_sequence (ctx:=ctx) (s:=xs) (RegisterUpdate.executes xs.core .sub ap r r
    (vx.2.1 ap (by simp)) (vx.2.1 r (by simp)) (vx.2.1 r (by simp))) running
  have last := PreconditionUpdate.executes (ctx:=ctx) rs running
    (vr.2.1 diagonal (by simp)) vr.2.2 (vr.2.1 z (by simp))
  have joined : Flow.Sequence ctx (body alpha p x ap r diagonal boundary z) s
      (finish ctx s alpha p x ap r diagonal boundary z xm xv rm rv (encode (PreconditionUpdate.result rs.core diagonal boundary))) :=
    Flow.sequence_append (Flow.sequence_append (Flow.sequence_append first second) third) last
  exact ⟨_,joined,(Flow.sequence_running joined body_segment).trans running⟩

theorem entry_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (live : Kernel.Residual.live ctx count)
    (valid : Valid (Assembly.setup ctx count s).core alpha p x ap r diagonal boundary z) :
    ∃ final, Flow.Runs ctx (entry count alpha p x ap r diagonal boundary z) s final ∧ final.halted=true := by
  obtain ⟨middle,bodyRun,_⟩ := body_exists (ctx:=ctx) (Assembly.setup ctx count s) (Assembly.setup_active (s:=s) live) valid
  exact ⟨_,VectorFlowEntry.executes pc running live body_segment bodyRun,rfl⟩

theorem inactive (actual : Flow.Runs ctx (entry count alpha p x ap r diagonal boundary z) s final)
    (pc : s.core.pc=0) (running : s.halted=false) (done : final.halted=true)
    (inactive : ¬Kernel.Residual.live ctx count) : final.core.global=s.core.global := by
  rw [VectorFlowEntry.inactive actual pc running done inactive]
  rfl

theorem inactive_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (inactive : ¬Kernel.Residual.live ctx count) :
    ∃ final, Flow.Runs ctx (entry count alpha p x ap r diagonal boundary z) s final ∧ final.halted=true :=
  ⟨_,VectorFlowEntry.setup_run pc running,Assembly.setup_inactive inactive⟩

end PtxTorchLean.Poisson.PTX.UpdateXRZ
