import PoissonPTX.CellEntryProducers
import PoissonPTX.CellEntryHistory
import PoissonPTX.BarrierValue

namespace PtxTorchLean.Poisson.PTX.CellEntry.Producers
open Ptx

variable {cfg : Concurrent.Config 32} {bases : Space → Word} {cell : BitVec 32}
  {width : Nat} {cells source : Word} {s t : State 32}
  {events : List (Concurrent.Event 32)} {indices : List (Fin 32 × IndexSources.Access)}
  {memory : Space → Memory} {chosen : Nat → Fin 8 → Sources.Origin Nat}
  {selected : Nat → Fin 4 → Sources.Origin Nat}

/- These are the entry theorem's execution, input representation and safety
premises, shared by the producer lemmas below. None asserts a store or answer. -/
variable (run : Runs cfg (CellPrologue.threadContext bases cell) (program width cells source) s events indices t)
  (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
  (words : Concurrent.Visibility.Compatible memory events chosen)
  (indexSources : IndexSources.Compatible (memory .global) events indices selected)
  (pcs : ∀ u, (s.core.lanes u).pc=0) (done : ∀ u, (t.core.lanes u).pc=21)
  (positive : 0<width) (fits : width*width<2^32)
  (space : (bases .shared).toNat+7*width*width*8≤2^64)
  (valid : ∀ u : Fin 32, u.val<width*width →
    CellGather.Valid (Local.beforeGather (CellPrologue.threadContext bases cell u) width (lane s u)) width cells source)

include run aligned initial words indexSources pcs done positive fits space valid

/-- Modular continuation theorem. A real first-barrier completion orders the
actual gathered producer before a later read. The continuation must preserve
this slot, expressed as byte disjointness of its stores. This structural premise
is separate from the read-value conclusion and must be derived from body code. -/
theorem read_gathered {later : List (Concurrent.Event 32)} {r : Nat}
    (reset : s.core.barrier=Barrier.reset generation)
    (joint : Concurrent.Visibility.Compatible memory (events++later) allSources)
    (performed : Concurrent.Visibility.Performed (events++later) allSources)
    (owner : Fin 32) (active : owner.val<width*width)
    (observed : later[r]?=some (.data reader access))
    (read : access.data.store=false) (shared : access.space=.shared)
    (address : access.data.address=(bases .shared).toNat+owner.val*8)
    (preserved : ∀ writer a, Concurrent.Event.data writer a∈later → a.data.store=true →
      a.space=.shared → Sources.Disjoint a.data.address ((bases .shared).toNat+owner.val*8)) :
    access.data.value=value bases cell width cells source s owner := by
  obtain ⟨w,wa,hw,write,sw,pc,waAddress,waValue⟩ :=
    producer run aligned initial words indexSources pcs done positive fits space valid owner active
  obtain ⟨allPC,site,generation',key,barrier,keySite,completion⟩ :=
    completed_barrier run aligned (fun u => by rw [pcs]; omega) owner (by rw [done]; omega)
  obtain ⟨c,hc⟩ := List.mem_iff_getElem?.mp completion
  obtain ⟨a,ha,hwa,hac⟩ := store_before_completion run reset hw write hc
  have wb := (List.getElem?_eq_some_iff.mp hw).1
  have ab := (List.getElem?_eq_some_iff.mp ha).1
  have cb := (List.getElem?_eq_some_iff.mp hc).1
  have jointWrite : (events++later)[w]?=some (.data owner wa) := by
    simpa only [List.getElem?_append,ite_eq_left wb] using hw
  have jointRead : (events++later)[events.length+r]?=some (.data reader access) := by
    simp [List.getElem?_append,observed]
  have across : Concurrent.Visibility.Across (events++later) w (events.length+r) := by
    refine ⟨owner,reader,wa,access,key,a,c,jointWrite,jointRead,?_,?_,hwa,hac,by omega⟩
    · simpa only [List.getElem?_append,ite_eq_left ab] using ha
    · simpa only [List.getElem?_append,ite_eq_left cb] using hc
  apply Concurrent.Visibility.read_from_value joint performed jointWrite jointRead write read sw shared
    (waAddress.trans address.symm) across
  intro other writer a atStore store sharedStore j k overlap
  rcases List.mem_append.mp (List.mem_of_getElem? atStore) with early | late
  · obtain ⟨same,offset,stored⟩ := byte_owner run aligned initial words indexSources pcs done
      positive fits space valid early store owner j k (by simpa [address] using overlap)
    rw [stored,offset]
  · have disjoint := preserved writer a late store sharedStore
    rw [Sources.Disjoint] at disjoint
    rw [address] at overlap
    have := j.isLt; have := k.isLt
    omega

end PtxTorchLean.Poisson.PTX.CellEntry.Producers
