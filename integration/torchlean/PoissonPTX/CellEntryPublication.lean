import PoissonPTX.SourceCut
import PoissonPTX.CellEntryContinuation

namespace PtxTorchLean.Poisson.PTX.CellEntry
open Ptx

/-- A memory view assembled from actual completed lane memories. It is used
only to rebase source proofs, never to mutate the candidate execution. -/
def publication (width : Nat) (small : width*width≤32) (bases : Space → Word)
    (initial : Space → Memory) (ready : State 32) : Space → Memory
  | .global => initial .global
  | .shared => SharedPlane.publish (initial .shared) (bases .shared).toNat width 0
      (fun i => ready.core.lanes (i.castLE small)) (List.finRange (width*width))

/-- Reading the accounting view recovers the actual owner's post-gather bytes. -/
theorem publication_lane (small : width*width≤32) (owner : Fin 32) (active : owner.val<width*width) :
    read64 (publication width small bases memory t .shared) ((bases .shared).toNat+owner.val*8)=
      read64 (t.core.lanes owner).shared ((bases .shared).toNat+owner.val*8) := by
  let i : Fin (width*width) := ⟨owner.val,active⟩
  have cast : i.castLE small=owner := Fin.ext rfl
  have word := SharedPlane.published_word (memory .shared) (bases .shared).toNat width 0
    (fun j => t.core.lanes (j.castLE small)) (List.finRange (width*width)) i (by simp)
  change read64 (publication width small bases memory t .shared) (SharedPlane.address _ width 0 i.val)=_ at word
  simpa only [SharedPlane.address,Nat.zero_mul,Nat.zero_add,i,cast] using word

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

/-- The published word is read from the actual lane's final shared bytes. -/
theorem publication_word (small : width*width≤32) (owner : Fin 32) (active : owner.val<width*width) :
    read64 (publication width small bases memory t .shared) ((bases .shared).toNat+owner.val*8)=
      Producers.value bases cell width cells source s owner := by
  have word := publication_lane (bases:=bases) (memory:=memory) (t:=t) small owner active
  obtain ⟨w,a,hw,store,shared,pc,address,value⟩ :=
    Producers.producer run aligned initial words indexSources pcs done positive fits space valid owner active
  have recorded := (recorded_store run (List.mem_of_getElem? hw) store).2.2.2.2
  rw [address,value] at recorded
  exact word.trans recorded

/-- The whole snapshot contract is derived from real store coverage and values;
bytes not covered by a prefix store keep their original initialization. -/
theorem publication_sound (small : width*width≤32) :
    Concurrent.SourceCut.Published memory (publication width small bases memory t) events := by
  constructor
  · intro writer access member store k
    have info := Producers.info run aligned initial words indexSources pcs done positive fits space valid member store
    have word := publication_word run aligned initial words indexSources pcs done positive fits space valid small writer info.1
    have bytes := congrArg (fun v => byte v k.val) word
    rw [Sources.byte_read64] at bytes
    rw [info.2.1,info.2.2.1,info.2.2.2]
    exact bytes
  · intro sp p uncovered
    cases sp with
    | global => rfl
    | shared =>
      apply SharedPlane.published_outside
      intro i
      by_contra inside
      let owner : Fin 32 := i.castLE small
      have active : owner.val<width*width := i.isLt
      obtain ⟨w,a,hw,store,shared,pc,address,value⟩ :=
        Producers.producer run aligned initial words indexSources pcs done positive fits space valid owner active
      have atSlot : a.data.address=SharedPlane.address (bases .shared).toNat width 0 i.val := by
        simpa [SharedPlane.address,owner] using address
      have bound : p-a.data.address<8 := by rw [atSlot]; omega
      exact uncovered ⟨owner,a,List.mem_of_getElem? hw,store,shared,⟨p-a.data.address,bound⟩,by simp; omega⟩

omit initial words indexSources positive fits space valid

/-- The publication cut is justified by actual first-barrier records. -/
theorem publication_ordered (reset : s.core.barrier=Barrier.reset generation) :
    Concurrent.SourceCut.Ordered events := by
  obtain ⟨allPC,site,generation',key,barrier,keySite,completion⟩ :=
    completed_barrier run aligned (fun u => by rw [pcs]; omega) (0 : Fin 32) (by rw [done]; omega)
  obtain ⟨c,hc⟩ := List.mem_iff_getElem?.mp completion
  refine ⟨c,key,hc,?_⟩
  intro w writer access observed store
  exact ⟨(recorded_store run (List.mem_of_getElem? observed) store).1,
    store_before_completion run reset observed store hc⟩

end PtxTorchLean.Poisson.PTX.CellEntry
