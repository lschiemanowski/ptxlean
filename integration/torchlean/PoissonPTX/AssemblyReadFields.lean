import PoissonPTX.AssemblyReadSites
import PoissonPTX.AssemblyOffsetSources
import PoissonPTX.AssemblyObservedBounds
import PoissonPTX.AssemblyObservedIndexBound

namespace PtxTorchLean.Poisson.PTX.Assembly
open ObservedAddress
variable {n : Nat} {a : Arena n} {thread : Fin n} {memory : Memory}
  {s t : Flow.State} {read : IndexSources.Access}

theorem Arena.loop_index_field
    (step : Flow.Observed.Step (a.context thread)
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output) s t access (some read))
    (which : read.pc=21) (contents : a.Contents memory)
    (bounds : BoundsReady (a.offset memory (thread.val+1)) s)
    (addresses : ReadAddressReady (a.context thread) a.entries a.element mask a.boundary s) :
    cursor s.core<a.entryCount ∧ read.address=a.base.toNat+a.entries.toNat+cursor s.core*4 := by
  obtain ⟨atPC,location,_⟩ := index_site step
  have pc : s.core.pc=21 := atPC.symm.trans which
  have bounded : cursor s.core<a.entryCount :=
    lt_of_lt_of_le (bounds.2.2.2 (by omega) (by omega)) (contents.last thread.val thread.isLt)
  refine ⟨bounded,?_⟩
  rw [location,addresses.2.2.1 pc]
  change (address32 a.base (Kernel.u32 (s.core.regs 19)) a.entries).toNat=_
  rw [address32_exact _ _ _ (by
    change a.base.toNat+cursor s.core*4+a.entries.toNat<2^64
    have := a.entriesFit; have := a.noWrap; omega)]
  change a.base.toNat+cursor s.core*4+a.entries.toNat=_
  omega

theorem Arena.boundary_field
    (step : Flow.Observed.Step (a.context thread)
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output) s t access (some read))
    (which : read.pc=32) (enabled : mask=true)
    (addresses : ReadAddressReady (a.context thread) a.entries a.element mask a.boundary s) :
    read.address=a.base.toNat+a.boundary.toNat+thread.val*4 := by
  obtain ⟨atPC,location,_⟩ := index_site step
  have pc : s.core.pc=32 := atPC.symm.trans which
  rw [location,addresses.2.2.2.2.2.2.2.2 enabled pc]
  change (address32 a.base (Kernel.Residual.index (a.context thread)) a.boundary).toNat=_
  rw [address32_exact _ _ _ (by rw [a.index]; have := a.boundaryFit; have := a.noWrap; have := thread.isLt; omega),a.index]
  omega

theorem Arena.element_field {word : Concurrent.Access}
    (step : Flow.Observed.Step (a.context thread)
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output) s t (some word) indexRecord)
    (load : word.data.store=false) (bounded : IndexReady a.elementCount s)
    (addresses : ReadAddressReady (a.context thread) a.entries a.element mask a.boundary s) :
    word.space=.global ∧ ∃ k, k<a.elementCount ∧ word.data.address=a.base.toNat+a.element.toNat+k*8 := by
  obtain ⟨global,pc,location⟩ := word_site step load
  have inside : (Kernel.u32 (s.core.regs 13)).toNat<a.elementCount := bounded (by omega) (by omega)
  refine ⟨global,_,inside,?_⟩
  rw [location,addresses.2.2.2.2.2.1 pc]
  change (address64 a.base (Kernel.u32 (s.core.regs 13)) a.element).toNat=_
  rw [address64_exact _ _ _ (by have := a.elementFit; have := a.noWrap; omega)]
  omega

end PtxTorchLean.Poisson.PTX.Assembly
