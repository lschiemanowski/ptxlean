import PoissonPTX.DotPublicationValue

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- For a real 256-lane launch, modular address preparation names the lane's
own eight-byte shared slot, with no wraparound. -/
theorem publication_location (scratch : Word) (lane : BitVec 32)
    (within : lane.toNat<256) (noWrap : scratch.toNat+2048≤2^64) :
    (scratch+BitVec.ofNat 64 (lane.toNat*8)).toNat=scratch.toNat+lane.toNat*8 := by
  have scaled : lane.toNat*8<2^64 := by omega
  have total : scratch.toNat+lane.toNat*8<2^64 := by omega
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt scaled,Nat.mod_eq_of_lt total]

theorem publication_memory_bound {access : Access} {scratch : Word} {lane : BitVec 32}
    (location : access.data.address=(scratch+BitVec.ofNat 64 (lane.toNat*8)).toNat)
    (within : lane.toNat<256) (aligned : scratch.toNat%8=0)
    (noWrap : scratch.toNat+2048≤2^64) : Valid64 scratch.toNat 2048 access.data.address := by
  rw [location,publication_location scratch lane within noWrap]
  exact ⟨by omega,by simp [Nat.add_mod,aligned],by omega,noWrap⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
