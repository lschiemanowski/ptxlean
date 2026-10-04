import PoissonPTX.NativeFlowAccessOrder
import PoissonPTX.ReductionStageSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
open Visibility.Repeated Reduction

variable {n : Nat} {cfg : Config n} {ctx : Fin n → Kernel.Context}
  {start final : State n} {events : List (Event n)} {owner reader : Fin n}
  {w r : Nat} {wa ra : Access}

/-- Source selection uses physical lane ownership and the actual suffix
instruction order. Prefix loops are allowed and cannot replace suffix stores. -/
theorem own_writers_around
    (run : Runs cfg ctx program start events indices final) (forward : ForwardFrom program cut)
    (stores : StageStores events base site) (suffix : ∀ stage, cut≤site stage)
    (hw : events[w]?=some (.data owner wa)) (hr : events[r]?=some (.data owner ra))
    (address : ra.data.address=base+owner.val*8)
    (gap : ∀ (other : Nat) (access : Access), events[other]?=some (.data owner access) →
      access.data.store=true → access.space=.shared →
      access.data.pc≤wa.data.pc ∨ ra.data.pc<access.data.pc)
    (readSuffix : cut≤ra.data.pc) : WritersAround events w r ra.data.address := by
  intro other thread access found store space j k overlap
  have same := owner_of_overlap stores.1 found store space (j:=j) (k:=k) (by simpa [address] using overlap)
  subst thread
  obtain ⟨stage,pc,_⟩ := stores.2 other owner access found store space
  have accessSuffix : cut≤access.data.pc := pc ▸ suffix stage
  rcases gap other access found store space with old | later
  · rcases lt_or_eq_of_le old with lt | eq
    · exact Or.inr (Or.inl (before_of_pc run forward found hw accessSuffix lt))
    · exact Or.inl (access_unique run forward found hw accessSuffix eq)
  · exact Or.inr (Or.inr (before_of_pc run forward hr found readSuffix later))

theorem neighbor_writers_around
    (run : Runs cfg ctx program start events indices final) (forward : ForwardFrom program cut)
    (stores : StageStores events base site) (suffix : ∀ stage, cut≤site stage)
    (hw : events[w]?=some (.data owner wa)) (address : ra.data.address=base+owner.val*8)
    (last : ∀ (other : Nat) (access : Access), events[other]?=some (.data owner access) →
      access.data.store=true → access.space=.shared → access.data.pc≤wa.data.pc) :
    WritersAround events w r ra.data.address := by
  intro other thread access found store shared j k overlap
  have same := owner_of_overlap stores.1 found store shared (j:=j) (k:=k) (by simpa [address] using overlap)
  subst thread
  obtain ⟨stage,pc,_⟩ := stores.2 other owner access found store shared
  have accessSuffix : cut≤access.data.pc := pc ▸ suffix stage
  rcases lt_or_eq_of_le (last other access found store shared) with lt | eq
  · exact Or.inr (Or.inl (before_of_pc run forward found hw accessSuffix lt))
  · exact Or.inl (access_unique run forward found hw accessSuffix eq)

theorem stage_own_read
    (run : Runs cfg ctx program start events indices final) (forward : ForwardFrom program cut)
    (stores : StageStores events base site) (sites : StrictMono site) (suffix : ∀ stage, cut≤site stage)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (stage : Fin 8) (hw : events[w]?=some (.data owner wa)) (hr : events[r]?=some (.data owner ra))
    (write : wa.data.store=true) (read : ra.data.store=false) (sw : wa.space=.shared) (sr : ra.space=.shared)
    (address : ra.data.address=base+owner.val*8)
    (previous : wa.data.pc=site ⟨stage.val,by omega⟩) (before : wa.data.pc<ra.data.pc)
    (next : ra.data.pc<site ⟨stage.val+1,by omega⟩) :
    ra.data.value=wa.data.value ∧ ∀ k, source r k=.store w k := by
  have writeSuffix : cut≤wa.data.pc := previous ▸ suffix _
  exact read_from_stage compatible ordered hw hr write read sw sr
    ((stores.1 w owner wa hw write sw).trans address.symm)
    (before_of_pc run forward hw hr writeSuffix before)
    (own_writers_around run forward stores suffix hw hr address
      (fun _ _ found store shared => own_gap stores sites stage previous next found store shared) (by omega))

theorem stage_neighbor_read
    (run : Runs cfg ctx program start events indices final) (forward : ForwardFrom program cut)
    (stores : StageStores events base site) (sites : StrictMono site) (suffix : ∀ stage, cut≤site stage)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (stage : Fin 8) (hw : events[w]?=some (.data owner wa)) (hr : events[r]?=some (.data reader ra))
    (write : wa.data.store=true) (read : ra.data.store=false) (sw : wa.space=.shared) (sr : ra.space=.shared)
    (address : ra.data.address=base+owner.val*8)
    (previous : wa.data.pc=site ⟨stage.val,by omega⟩)
    (inactive : active ⟨stage.val+1,by omega⟩≤owner.val) (across : Visibility.Across events w r) :
    ra.data.value=wa.data.value ∧ ∀ k, source r k=.store w k :=
  read_from_stage compatible ordered hw hr write read sw sr
    ((stores.1 w owner wa hw write sw).trans address.symm) (.edge (.inr across))
    (neighbor_writers_around run forward stores suffix hw address
      (fun _ _ found store shared => neighbor_last stores sites stage previous inactive found store shared))

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
