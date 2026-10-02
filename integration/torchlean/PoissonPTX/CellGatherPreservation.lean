import PoissonPTX.CellConsumerSources
import PoissonPTX.CellTailProgram

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer
open CellMiddle

/-- The arithmetic body's first instruction is a guard, not a store. -/
theorem no_access_zero (run : Runs cfg (program width) start events final)
    (member : Event.data thread access∈events) : access.data.pc≠0 := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨same,op,next,fetch,hd⟩ := step_access_origin hs hm
  intro zero
  have pc := (access_pc hd).symm.trans zero
  rw [pc] at fetch
  simp [program,Checks.program,code,phase] at fetch

/-- Every arithmetic shared store lies in planes one through six. Plane zero
is the gathered input, and its bytes are never overwritten by this body. -/
theorem preserves_gather (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (member : Event.data writer access∈events) (store : access.data.store=true) (shared : access.space=.shared)
    (owner : Fin 32) (active : owner.val<width*width) :
    Sources.Disjoint access.data.address ((bases .shared).toNat+owner.val*8) := by
  obtain ⟨index,observed⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨plane,live,pc,address⟩ := coverage launch lo hi run index writer access observed store shared
  have positive : plane≠0 := by
    intro zero
    have zeroPC : access.data.pc=0 := by simpa [zero,site] using pc
    exact no_access_zero run member zeroPC
  have afterInput := Geometry.plane_positive width writer.val (bases .shared).toNat plane positive
  have ownerEnd := (Geometry.plane_zero width owner.val (bases .shared).toNat active).2
  rw [address,Sources.Disjoint]
  simp only [SharedPlane.address,Nat.zero_mul,Nat.zero_add] at ownerEnd
  exact Or.inr (by omega)

namespace WithOutput

/-- The real output tail only adds global stores. Projecting its retained
arithmetic records therefore derives the same shared-input preservation. -/
theorem preserves_gather (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (member : Event.data writer access∈events) (store : access.data.store=true) (shared : access.space=.shared)
    (owner : Fin 32) (active : owner.val<width*width) :
    Sources.Disjoint access.data.address ((bases .shared).toNat+owner.val*8) := by
  obtain ⟨small,shadow,actual,embedding,omitted,related⟩ := arithmetic_filtered lo hi run launch.aligned launch.pcs
  obtain ⟨index,observed⟩ := List.mem_iff_getElem?.mp member
  have kept : Projection.Retained embedding index := by
    by_contra absent
    have global := (omitted index (.data writer access) observed absent).1
    simp_all
  obtain ⟨r,bound,atIndex⟩ := kept
  have inSmall : small[r]?=some (.data writer access) := by
    rw [← embedding.fetch r bound,atIndex,observed]
  exact CellConsumer.preserves_gather launch lo hi actual (List.mem_of_getElem? inSmall) store shared owner active

end WithOutput
end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer
