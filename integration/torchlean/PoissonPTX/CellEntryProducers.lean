import PoissonPTX.CellEntryStoreValue

namespace PtxTorchLean.Poisson.PTX.CellEntry.Producers

def value (bases : Space → Word) (cell : BitVec 32) (width : Nat) (cells source : Word)
    (s : State 32) (owner : Fin 32) : Word :=
  CellGather.value (Local.beforeGather (CellPrologue.threadContext bases cell owner) width (lane s owner)) width cells source

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

/-- Padding cannot produce a store. Every recorded writer has the physical
lane slot and value computed from its actual connectivity/source bytes. -/
theorem info (member : Concurrent.Event.data owner access∈events) (store : access.data.store=true) :
    owner.val<width*width ∧ access.space=.shared ∧
    access.data.address=(bases .shared).toNat+owner.val*8 ∧
    access.data.value=value bases cell width cells source s owner := by
  have active := store_active run aligned initial words indexSources (pcs owner) positive fits member store
  have ownerActive : owner.val<width*width := by simpa only [context_lane] using active
  have result := recorded_gather run aligned initial words indexSources (pcs owner) (done owner)
    positive fits active (valid owner ownerActive) member store
  exact ⟨ownerActive,(recorded_store run member store).1,
    result.1.trans (destination_address bases cell owner _ ownerActive space),result.2⟩

theorem producer (owner : Fin 32) (active : owner.val<width*width) :
    ∃ (position : Nat) (access : Concurrent.Access), events[position]?=some (.data owner access) ∧
      access.data.store=true ∧ access.space=.shared ∧ access.data.pc=19 ∧
      access.data.address=(bases .shared).toNat+owner.val*8 ∧
      access.data.value=value bases cell width cells source s owner := by
  obtain ⟨a,member,store,shared⟩ := completed_wrote run aligned initial words indexSources owner
    (pcs owner) (done owner) positive fits (by simpa only [context_lane] using active) (valid owner active)
  have details := info run aligned initial words indexSources pcs done positive fits space valid member store
  obtain ⟨position,observed⟩ := List.mem_iff_getElem?.mp member
  exact ⟨position,a,observed,store,shared,(recorded_store run member store).2.1,details.2.2.1,details.2.2.2⟩

/-- Each byte of a lane's slot can only be supplied by that same lane, with
the same within-word offset. Merely different starting addresses would not suffice. -/
theorem byte_owner (member : Concurrent.Event.data writer access∈events) (store : access.data.store=true)
    (owner : Fin 32) (j k : Fin 8)
    (same : access.data.address+j.val=(bases .shared).toNat+owner.val*8+k.val) :
    writer=owner ∧ j=k ∧ access.data.value=value bases cell width cells source s owner := by
  have details := info run aligned initial words indexSources pcs done positive fits space valid member store
  rw [details.2.2.1] at same
  have w : writer.val=owner.val := by have := j.isLt; have := k.isLt; omega
  have jk : j.val=k.val := by omega
  have equal := Fin.ext w
  subst writer
  exact ⟨rfl,Fin.ext jk,details.2.2.2⟩

theorem different_writers (left : Concurrent.Event.data a wa∈events) (leftStore : wa.data.store=true)
    (right : Concurrent.Event.data b wb∈events) (rightStore : wb.data.store=true) (different : a≠b) :
    Sources.Disjoint wa.data.address wb.data.address := by
  have x := info run aligned initial words indexSources pcs done positive fits space valid left leftStore
  have y := info run aligned initial words indexSources pcs done positive fits space valid right rightStore
  have different' : a.val≠b.val := fun eq => different (Fin.ext eq)
  rw [Sources.Disjoint,x.2.2.1,y.2.2.1]
  omega

end PtxTorchLean.Poisson.PTX.CellEntry.Producers
