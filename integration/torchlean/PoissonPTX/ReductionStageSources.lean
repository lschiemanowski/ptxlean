import PoissonPTX.ReductionSources

/-! Source selection for the shrinking eight-stage reduction tree. Stage zero
publishes the initial 256 lane sums; stages one through eight replace the first
128, 64, ..., 1 words. Store coverage is a control obligation, not a value axiom. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction
open Visibility.Repeated

/-- Active stores at each publication, including the initial lane sums. -/
def active (stage : Fin 9) : Nat := 256 / 2^stage.val

theorem active_antitone : ∀ a b : Fin 9, a≤b → active b≤active a := by decide +kernel

/-- All shared stores have one of the nine publication sites and belong to
an active lane. A concrete kernel must derive this from fetched control. -/
def StageStores (events : List (Event n)) (base : Nat) (site : Fin 9 → Nat) : Prop :=
  LaneStores events base ∧ ∀ (index : Nat) (thread : Fin n) (access : Access),
    events[index]?=some (.data thread access) → access.data.store=true → access.space=.shared →
    ∃ stage, access.data.pc=site stage ∧ thread.val<active stage

variable {n : Nat} {events : List (Event n)} {other : Nat}
  {owner : Fin n} {wa ra access : Access}

/-- There is no store site between consecutive tree publications. -/
theorem own_gap (stores : StageStores events base site) (ordered : StrictMono site)
    (stage : Fin 8) (previous : wa.data.pc=site ⟨stage.val,by omega⟩)
    (next : ra.data.pc<site ⟨stage.val+1,by omega⟩)
    (found : events[other]?=some (.data owner access))
    (write : access.data.store=true) (shared : access.space=.shared) :
    access.data.pc≤wa.data.pc ∨ ra.data.pc<access.data.pc := by
  obtain ⟨q,pc,live⟩ := stores.2 other owner access found write shared
  by_cases before : q.val≤stage.val
  · left; rw [pc,previous]; exact ordered.monotone before
  · right
    have after : site ⟨stage.val+1,by omega⟩≤site q := ordered.monotone (by change stage.val+1≤q.val; omega)
    omega

/-- The right-hand lane is outside the current active range. It cannot write
at this stage or any later stage, because active ranges only shrink. -/
theorem neighbor_last (stores : StageStores events base site) (ordered : StrictMono site)
    (stage : Fin 8) (previous : wa.data.pc=site ⟨stage.val,by omega⟩)
    (inactive : active ⟨stage.val+1,by omega⟩≤owner.val)
    (found : events[other]?=some (.data owner access))
    (write : access.data.store=true) (shared : access.space=.shared) :
    access.data.pc≤wa.data.pc := by
  obtain ⟨q,pc,live⟩ := stores.2 other owner access found write shared
  have earlier : q.val≤stage.val := by
    by_contra h
    have bounds := active_antitone ⟨stage.val+1,by omega⟩ q (by change stage.val+1≤q.val; omega)
    omega
  rw [pc,previous]
  exact ordered.monotone earlier

variable {w r : Nat} {reader : Fin n}

/-- Complete own-read selection from phase coverage, with no WritersAround or
assumed source/value premise. Earlier same-lane writes follow program order. -/
theorem stage_own_read (run : Runs cfg program start events final) (forward : Forward program)
    (stores : StageStores events base site) (sites : StrictMono site)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (stage : Fin 8) (hw : events[w]?=some (.data owner wa))
    (hr : events[r]?=some (.data owner ra))
    (write : wa.data.store=true) (read : ra.data.store=false)
    (sw : wa.space=.shared) (sr : ra.space=.shared)
    (address : ra.data.address=base+owner.val*8)
    (previous : wa.data.pc=site ⟨stage.val,by omega⟩) (before : wa.data.pc<ra.data.pc)
    (next : ra.data.pc<site ⟨stage.val+1,by omega⟩) :
    ra.data.value=wa.data.value ∧ ∀ k, source r k=.store w k :=
  own_read run forward stores.1 compatible ordered hw hr write read sw sr address before
    (fun _ _ found store shared => own_gap stores sites stage previous next found store shared)

/-- Complete neighbor-read selection from shrinking active ranges and an
actual barrier edge. No future publication can replace this neighbor word. -/
theorem stage_neighbor_read (run : Runs cfg program start events final) (forward : Forward program)
    (stores : StageStores events base site) (sites : StrictMono site)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (stage : Fin 8) (hw : events[w]?=some (.data owner wa))
    (hr : events[r]?=some (.data reader ra))
    (write : wa.data.store=true) (read : ra.data.store=false)
    (sw : wa.space=.shared) (sr : ra.space=.shared)
    (address : ra.data.address=base+owner.val*8)
    (previous : wa.data.pc=site ⟨stage.val,by omega⟩)
    (inactive : active ⟨stage.val+1,by omega⟩≤owner.val)
    (across : Visibility.Across events w r) :
    ra.data.value=wa.data.value ∧ ∀ k, source r k=.store w k :=
  neighbor_read run forward stores.1 compatible ordered hw hr write read sw sr address across
    (fun _ _ found store shared => neighbor_last stores sites stage previous inactive found store shared)

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction
