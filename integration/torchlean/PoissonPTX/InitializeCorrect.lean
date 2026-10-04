import PoissonPTX.InitializeValues

namespace PtxTorchLean.Poisson.PTX.Initialize

/-- Physical separation of all outputs and the diagonal read after the copies. -/
structure Separate (s : State) (rhs r diagonal z p x : Word) : Prop where
  rhs_r : Sources.Disjoint (address s 12 rhs).toNat (address s 12 r).toNat
  rhs_z : Sources.Disjoint (address s 12 rhs).toNat (address s 12 z).toNat
  rhs_p : Sources.Disjoint (address s 12 rhs).toNat (address s 12 p).toNat
  rhs_x : Sources.Disjoint (address s 12 rhs).toNat (address s 12 x).toNat
  r_z : Sources.Disjoint (address s 12 r).toNat (address s 12 z).toNat
  r_p : Sources.Disjoint (address s 12 r).toNat (address s 12 p).toNat
  r_x : Sources.Disjoint (address s 12 r).toNat (address s 12 x).toNat
  z_p : Sources.Disjoint (address s 12 z).toNat (address s 12 p).toNat
  z_x : Sources.Disjoint (address s 12 z).toNat (address s 12 x).toNat
  p_x : Sources.Disjoint (address s 12 p).toNat (address s 12 x).toNat
  rhsD : Sources.Disjoint (address s 12 rhs).toNat (address s 12 diagonal).toNat
  rD : Sources.Disjoint (address s 12 r).toNat (address s 12 diagonal).toNat

/-- The complete initialization masks the actual input, copies it to rhs and r,
stores one quotient word to z and p, and writes a positive zero word to x. -/
theorem correct (actual : Flow.Sequence ctx (body boundary input rhs r diagonal z p x) s final)
    (running : s.halted=false) (valid : Valid s.core boundary input rhs r diagonal z p x)
    (separated : Separate s.core rhs r diagonal z p x) :
    read64 final.core.global (address s.core 12 rhs).toNat=loadWord s.core boundary input ∧
    read64 final.core.global (address s.core 12 r).toNat=loadWord s.core boundary input ∧
    decode (read64 final.core.global (address s.core 12 z).toNat)=quotient s.core boundary input diagonal ∧
    read64 final.core.global (address s.core 12 p).toNat=read64 final.core.global (address s.core 12 z).toNat ∧
    read64 final.core.global (address s.core 12 x).toNat=0 ∧
    (∀ byte, (∀ field∈[rhs,r,z,p,x], byte<(address s.core 12 field).toNat ∨ (address s.core 12 field).toNat+8≤byte) →
      final.core.global byte=s.core.global byte) := by
  obtain ⟨value,state,valueEq⟩ := state_result actual running valid
  subst final
  rw [finish_global]
  simp only [read64_write64_disjoint _ _ _ _ separated.rhs_r.symm,
    read64_write64_disjoint _ _ _ _ separated.rhs_z.symm,
    read64_write64_disjoint _ _ _ _ separated.rhs_p.symm,
    read64_write64_disjoint _ _ _ _ separated.rhs_x.symm,
    read64_write64_disjoint _ _ _ _ separated.r_z.symm,
    read64_write64_disjoint _ _ _ _ separated.r_p.symm,
    read64_write64_disjoint _ _ _ _ separated.r_x.symm,
    read64_write64_disjoint _ _ _ _ separated.z_p.symm,
    read64_write64_disjoint _ _ _ _ separated.z_x.symm,
    read64_write64_disjoint _ _ _ _ separated.p_x.symm,read64_write64]
  refine ⟨True.intro,True.intro,valueEq.trans (ready_result separated.rhsD separated.rD),True.intro,True.intro,?_⟩
  intro byte outside
  rw [write64_outside _ _ _ _ (outside x (by simp)),
    write64_outside _ _ _ _ (outside p (by simp)),
    write64_outside _ _ _ _ (outside z (by simp)),
    write64_outside _ _ _ _ (outside r (by simp)),
    write64_outside _ _ _ _ (outside rhs (by simp))]

end PtxTorchLean.Poisson.PTX.Initialize
