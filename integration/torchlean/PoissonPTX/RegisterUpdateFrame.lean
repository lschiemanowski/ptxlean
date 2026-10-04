import PoissonPTX.RegisterUpdate
import PoissonPTX.Sources

namespace PtxTorchLean.Poisson.PTX.RegisterUpdate

theorem finish_global : (finish s input shift output mulWord value).global=
    write64 s.global (address s 12 output).toNat value := by
  simp [finish,loaded,left,put,assign,advance,addressed]

theorem finish_regs (different : reg≠1 ∧ reg≠2 ∧ reg≠5 ∧ reg≠6 ∧ reg≠10) :
    (finish s input shift output mulWord value).regs reg=s.regs reg := by
  simp [finish,loaded,left,put,assign,advance,addressed,different.1,different.2.1,
    different.2.2.1,different.2.2.2.1,different.2.2.2.2]

theorem finish_address : address (finish s input shift output mulWord value) 12 field=address s 12 field := by
  simp only [address,wide,finish_regs (by decide : (0:Nat)≠1 ∧ 0≠2 ∧ 0≠5 ∧ 0≠6 ∧ 0≠10),
    finish_regs (by decide : (12:Nat)≠1 ∧ 12≠2 ∧ 12≠5 ∧ 12≠6 ∧ 12≠10)]

theorem finish_frame :
    (finish s input shift output mulWord value).globalStart=s.globalStart ∧
    (finish s input shift output mulWord value).globalBytes=s.globalBytes ∧
    (finish s input shift output mulWord value).shared=s.shared ∧
    (finish s input shift output mulWord value).regs 6=value := by
  simp [finish,loaded,left,put,assign,advance,addressed]

/-- Later vector loads at disjoint addresses obtain the original bytes. -/
theorem finish_read (apart : Sources.Disjoint (address s 12 output).toNat (address s 12 field).toNat) :
    read64 (finish s input shift output mulWord value).global
      (address (finish s input shift output mulWord value) 12 field).toNat=
        read64 s.global (address s 12 field).toNat := by
  rw [finish_address,finish_global,read64_write64_disjoint _ _ _ _ apart]

end PtxTorchLean.Poisson.PTX.RegisterUpdate
