import PoissonPTX.UpdateXRZLayout

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ

theorem coefficient_global : (coefficient s alpha).core.global=s.core.global := rfl

theorem coefficient_word : (coefficient s alpha).core.regs 4=read64 s.core.global (s.core.regs 0+alpha).toNat := by
  simp [coefficient,ScalarLoad.loaded,assign,advance]

theorem solution_global : (solution s alpha p x xm xv).core.global=
    write64 s.core.global (address s.core 12 x).toNat xv := by
  simp only [solution,RegisterUpdate.finish_global,coefficient_global,coefficient_geometry.address]

theorem solution_word : (solution s alpha p x xm xv).core.regs 4=read64 s.core.global (s.core.regs 0+alpha).toNat := by
  simp only [solution,RegisterUpdate.finish_regs (by decide : (4:Nat)≠1 ∧ 4≠2 ∧ 4≠5 ∧ 4≠6 ∧ 4≠10),coefficient_word]

theorem residual_global : (residual s alpha p x ap r xm xv rm rv).core.global=
    write64 (write64 s.core.global (address s.core 12 x).toNat xv) (address s.core 12 r).toNat rv := by
  simp only [residual,RegisterUpdate.finish_global,solution_global,solution_geometry.address]

theorem residual_word : (residual s alpha p x ap r xm xv rm rv).core.regs 6=rv := RegisterUpdate.finish_frame.2.2.2

theorem finish_global : (finish ctx s alpha p x ap r diagonal boundary z xm xv rm rv zv).core.global=
    write64 (write64 (write64 s.core.global (address s.core 12 x).toNat xv)
      (address s.core 12 r).toNat rv) (address s.core 12 z).toNat zv := by
  simp only [finish,PreconditionUpdate.finish,put]
  simp only [addressed,assign,advance,PreconditionUpdate.ready_frame.1,residual_global,residual_geometry.address]

end PtxTorchLean.Poisson.PTX.UpdateXRZ
