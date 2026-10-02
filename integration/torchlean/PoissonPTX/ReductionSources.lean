import PoissonPTX.RepeatedShared
import PoissonPTX.ConcurrentOwnership

/-! Repeated in-place lane words. These theorems reduce visibility to physical
ownership and instruction positions; neither load results nor source choices
are premises of ownership. Kernel control must establish these conditions. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction
open Visibility.Repeated

variable {n : Nat} {events : List (Event n)} {index a b w r : Nat}
  {j k : Fin 8} {thread owner reader : Fin n} {access wa ra la : Access}

/-- All shared stores replace the eight-byte word owned by their lane. -/
def LaneStores (events : List (Event n)) (base : Nat) : Prop :=
  ∀ (index : Nat) (thread : Fin n) (access : Access), events[index]?=some (.data thread access) →
    access.data.store=true → access.space=.shared →
    access.data.address=base+thread.val*8

/-- Overlap of even one byte identifies the owning lane. -/
theorem owner_of_overlap (stores : LaneStores events base)
    (found : events[index]?=some (.data thread access))
    (store : access.data.store=true) (shared : access.space=.shared)
    (same : access.data.address+j.val=base+owner.val*8+k.val) :
    thread=owner := by
  have addr := stores index thread access found store shared
  have hj := j.isLt; have hk := k.isLt
  apply Fin.ext
  omega

/-- Fetched forward control reflects instruction order into actual occurrences.
It does not impose chronological order on different threads. -/
theorem before_of_pc (run : Runs cfg program start events final) (forward : Forward program)
    (left : events[a]?=some (.data thread la)) (right : events[b]?=some (.data thread ra))
    (pc : la.data.pc<ra.data.pc) : Before events a b := by
  obtain ⟨ha,ea⟩ := List.getElem?_eq_some_iff.mp left
  obtain ⟨hb,eb⟩ := List.getElem?_eq_some_iff.mp right
  have increasing := run_access_order run forward
  have lt : a<b := by
    rcases lt_trichotomy a b with lt | eq | gt
    · exact lt
    · subst b
      have same := Option.some.inj (left.symm.trans right)
      cases same
      omega
    · have wrong := increasing.rel_getElem_of_lt hb ha gt thread ra la eb ea
      omega
  exact .edge (.inl ⟨thread,la,ra,left,right,lt⟩)

/-- For an owner's own read, there is no intervening store instruction between
the selected previous write and that read. Later writes are ordered after it. -/
theorem own_writers_around (run : Runs cfg program start events final)
    (forward : Forward program) (stores : LaneStores events base)
    (hw : events[w]?=some (.data owner wa)) (hr : events[r]?=some (.data owner ra))
    (address : ra.data.address=base+owner.val*8)
    (gap : ∀ (other : Nat) (access : Access), events[other]?=some (.data owner access) →
      access.data.store=true → access.space=.shared →
      access.data.pc≤wa.data.pc ∨ ra.data.pc<access.data.pc) :
    WritersAround events w r ra.data.address := by
  intro other thread access found store shared j k overlap
  have same := owner_of_overlap stores found store shared (j:=j) (k:=k) (by simpa [address] using overlap)
  subst thread
  rcases gap other access found store shared with old | later
  · rcases lt_or_eq_of_le old with lt | eq
    · exact Or.inr (Or.inl (before_of_pc run forward found hw lt))
    · exact Or.inl (access_site_unique run forward found hw eq)
  · exact Or.inr (Or.inr (before_of_pc run forward hr found later))

/-- Once a neighbor lane is inactive, all its stores occur at or before the
selected site. Earlier stores are excluded using that owner's program order. -/
theorem neighbor_writers_around (run : Runs cfg program start events final)
    (forward : Forward program) (stores : LaneStores events base)
    (hw : events[w]?=some (.data owner wa))
    (address : ra.data.address=base+owner.val*8)
    (last : ∀ (other : Nat) (access : Access), events[other]?=some (.data owner access) →
      access.data.store=true → access.space=.shared → access.data.pc≤wa.data.pc) :
    WritersAround events w r ra.data.address := by
  intro other thread access found store shared j k overlap
  have same := owner_of_overlap stores found store shared (j:=j) (k:=k) (by simpa [address] using overlap)
  subst thread
  rcases lt_or_eq_of_le (last other access found store shared) with lt | eq
  · exact Or.inr (Or.inl (before_of_pc run forward found hw lt))
  · exact Or.inl (access_site_unique run forward found hw eq)

/-- Universal source and value selection for the own-word read. -/
theorem own_read (run : Runs cfg program start events final)
    (forward : Forward program) (stores : LaneStores events base)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (hw : events[w]?=some (.data owner wa)) (hr : events[r]?=some (.data owner ra))
    (write : wa.data.store=true) (read : ra.data.store=false)
    (sw : wa.space=.shared) (sr : ra.space=.shared)
    (address : ra.data.address=base+owner.val*8) (pc : wa.data.pc<ra.data.pc)
    (gap : ∀ (other : Nat) (access : Access), events[other]?=some (.data owner access) →
      access.data.store=true → access.space=.shared →
      access.data.pc≤wa.data.pc ∨ ra.data.pc<access.data.pc) :
    ra.data.value=wa.data.value ∧ ∀ k, source r k=.store w k :=
  read_from_stage compatible ordered hw hr write read sw sr
    ((stores w owner wa hw write sw).trans address.symm)
    (before_of_pc run forward hw hr pc)
    (own_writers_around run forward stores hw hr address gap)

/-- Universal source and value selection for a now-inactive neighbor. The
barrier edge is still derived separately from fetched arrivals/completion. -/
theorem neighbor_read (run : Runs cfg program start events final)
    (forward : Forward program) (stores : LaneStores events base)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (hw : events[w]?=some (.data owner wa)) (hr : events[r]?=some (.data reader ra))
    (write : wa.data.store=true) (read : ra.data.store=false)
    (sw : wa.space=.shared) (sr : ra.space=.shared)
    (address : ra.data.address=base+owner.val*8) (across : Visibility.Across events w r)
    (last : ∀ (other : Nat) (access : Access), events[other]?=some (.data owner access) →
      access.data.store=true → access.space=.shared → access.data.pc≤wa.data.pc) :
    ra.data.value=wa.data.value ∧ ∀ k, source r k=.store w k :=
  read_from_stage compatible ordered hw hr write read sw sr
    ((stores w owner wa hw write sw).trans address.symm) (.edge (.inr across))
    (neighbor_writers_around run forward stores hw address last)

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction
