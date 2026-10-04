import PoissonPTX.HostAssemblyLayout
import PoissonPTX.HostCellLayout

namespace PtxTorchLean.Poisson.PTX.Host
variable {n e w : Nat} {a : Layout n e w}

/-- Preserved bytes reconstruct exactly the same uploaded four-byte table word. -/
theorem Layout.Static.read32 (same : a.Static initial memory) (f : Field)
    (immutable : f.mutable=false) (width : f.width=4) (inside : k<f.count n e w) :
    read32 memory (a.slot f+k*4)=read32 initial (a.slot f+k*4) := by
  apply IndexSources.word_eq_of_bytes
  intro byte
  simp only [IndexSources.byte_read32]
  apply same f immutable
  · omega
  · have := byte.isLt
    rw [width]
    omega

theorem Layout.Static.connectivity (same : a.Static initial memory) (connected : a.Connectivity initial) :
    a.Connectivity memory := by
  intro k inside
  rw [same.read32 .cells rfl rfl inside]
  exact connected k inside

theorem Layout.Static.assembly (same : a.Static initial memory)
    (contents : (a.assembly false).Contents initial) : (a.assembly false).Contents memory := by
  have offset (k : Nat) (inside : k<n+1) :
      (a.assembly false).offset memory k=(a.assembly false).offset initial k := by
    exact congrArg BitVec.toNat (same.read32 .offsets rfl rfl inside)
  constructor
  · intro i inside
    rw [offset i (by omega),offset (i+1) (by omega)]
    exact contents.ordered i inside
  · intro i inside
    rw [offset (i+1) (by omega)]
    exact contents.last i inside
  · intro k inside
    have word := same.read32 .entries rfl rfl inside
    change PTX.read32 memory ((a.assembly false).base.toNat+(a.assembly false).entries.toNat+k*4)=_ at word
    rw [word]
    exact contents.indices k inside

end PtxTorchLean.Poisson.PTX.Host
