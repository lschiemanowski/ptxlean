import PoissonPTX.RestartVectorsState
import PoissonPTX.Sources

namespace PtxTorchLean.Poisson.PTX.RestartVectors

structure Separate (s : State) (r diagonal boundary z p : Word) : Prop where
  rD : Sources.Disjoint (address s 12 r).toNat (address s 12 diagonal).toNat
  rZ : Sources.Disjoint (address s 12 r).toNat (address s 12 z).toNat
  rP : Sources.Disjoint (address s 12 r).toNat (address s 12 p).toNat
  zP : Sources.Disjoint (address s 12 z).toNat (address s 12 p).toNat
  rB : (address s 12 r).toNat+8≤(Assembly.maskAddress s boundary).toNat ∨
    (Assembly.maskAddress s boundary).toNat+4≤(address s 12 r).toNat

def quotient (s : State) (source diagonal boundary : Word) : Float :=
  decode (read64 s.global (address s 12 source).toNat)/decode (PreconditionUpdate.divisor s diagonal boundary)

theorem divisor_value (separated : Separate s.core r diagonal boundary z p) :
    PreconditionUpdate.divisor (copied s source r).core diagonal boundary=PreconditionUpdate.divisor s.core diagonal boundary := by
  unfold PreconditionUpdate.divisor Assembly.maskFlag
  rw [copied_mask]
  simp only [copied,VectorCopy.finish_address,VectorCopy.finish_global]
  rw [read32_write64_disjoint _ _ _ _ separated.rB,read64_write64_disjoint _ _ _ _ separated.rD]

theorem ready_result (separated : Separate s.core r diagonal boundary z p) :
    DividePair.result (ready ctx s source r diagonal boundary).core=quotient s.core source diagonal boundary := by
  simp only [DividePair.result,ready_word,ready_divisor,divisor_value separated,quotient]

/-- Restart copies the actual fresh residual and computes the new z and p
from the boundary-adjusted diagonal, preserving every other byte. -/
theorem correct (actual : Flow.Sequence ctx (body source r diagonal boundary z p) s final)
    (running : s.halted=false) (valid : Valid s.core source r diagonal boundary z p)
    (separated : Separate s.core r diagonal boundary z p) :
    read64 final.core.global (address s.core 12 r).toNat=read64 s.core.global (address s.core 12 source).toNat ∧
    decode (read64 final.core.global (address s.core 12 z).toNat)=quotient s.core source diagonal boundary ∧
    read64 final.core.global (address s.core 12 p).toNat=read64 final.core.global (address s.core 12 z).toNat ∧
    (∀ byte, (∀ field∈[r,z,p], byte<(address s.core 12 field).toNat ∨ (address s.core 12 field).toNat+8≤byte) →
      final.core.global byte=s.core.global byte) := by
  obtain ⟨value,state,valueEq⟩ := state_result actual running valid
  subst final
  rw [finish_global]
  have pr : Sources.Disjoint (address s.core 12 p).toNat (address s.core 12 r).toNat := separated.rP.symm
  have zr : Sources.Disjoint (address s.core 12 z).toNat (address s.core 12 r).toNat := separated.rZ.symm
  have pz : Sources.Disjoint (address s.core 12 p).toNat (address s.core 12 z).toNat := separated.zP.symm
  rw [read64_write64_disjoint _ _ _ _ pr,read64_write64_disjoint _ _ _ _ zr,
    read64_write64_disjoint _ _ _ _ pz]
  simp only [read64_write64]
  refine ⟨True.intro,valueEq.trans (ready_result separated),True.intro,?_⟩
  intro byte outside
  rw [write64_outside _ _ _ _ (outside p (by simp)),write64_outside _ _ _ _ (outside z (by simp)),
    write64_outside _ _ _ _ (outside r (by simp))]

end PtxTorchLean.Poisson.PTX.RestartVectors
