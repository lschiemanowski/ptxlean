import PoissonPTX.ConcurrentOwnership
import PoissonPTX.BarrierChecks

namespace PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks
open Ptx
open Checks

/-- The old executable fragment now discharges ordering and event ownership
through the general control theorems, rather than a manually supplied path. -/
theorem forward : Forward program := by
  intro pc active target fetch
  have mem := List.mem_of_getElem? fetch
  simp [program,SharedStore.code] at mem
  obtain ⟨rfl,rfl⟩ := mem
  have pos : pc=0 := by
    cases pc with
    | zero => rfl
    | succ k =>
      have impossible := List.mem_of_getElem? (show ([Instr.data (.wide8 1 (.reg 14)),.data (.add64 2 (.reg 3) (.reg 1)),.data (.store64 .shared (.offset 2 0) (.reg 8)),.sync 0,.data (.load64 .shared 4 (.imm 0)),.sync 0])[k]?=some (.skip 1 4) from fetch)
      simp at impossible
  omega

theorem stops_writer : StopsFor program (0 : Fin 2) 3 := by
  intro pc active target fetch before
  have mem := List.mem_of_getElem? fetch
  simp [program,SharedStore.code] at mem
  obtain ⟨rfl,rfl⟩ := mem
  exact Or.inl (by decide)

theorem stops_barrier : StopsAt program 4 := by
  intro pc active target fetch before
  have mem := List.mem_of_getElem? fetch
  simp [program,SharedStore.code] at mem
  obtain ⟨rfl,rfl⟩ := mem
  decide

/-- Padding really can skip the store, so it cannot be used as its producer. -/
theorem padding_cannot_supply_store : ¬StopsFor program (1 : Fin 2) 3 := by
  intro h
  have bad := h 0 1 4 rfl (by decide)
  simp at bad

/-- A branch that also skipped the barrier would violate the ordering contract. -/
theorem bypass_rejected : ¬StopsAt [.skip 1 2,.sync 0] 1 := by
  intro h
  have bad := h 0 1 2 rfl (by decide)
  simp at bad

/-- For every candidate execution, a read at PC five has an earlier actual
store by lane zero and the full strict barrier path. -/
theorem every_schedule_order {events : List (Event 2)} {r : Nat}
    (run : Runs cfg program start events final)
    (read : events[r]?=some (Event.data reader access)) (pc : access.data.pc=5) :
    ∃ w wa, events[w]?=some (.data 0 wa) ∧ wa.data.pc=3 ∧
      wa.data.store=true ∧ wa.space=.shared ∧ Visibility.Across events w r := by
  exact producer_across run rfl (show program[3]?=some (.data (.store64 .shared (.offset 2 0) (.reg 8))) from rfl)
    stops_writer (by decide) (by decide) (show program[4]?=some (.sync 0) from rfl)
    stops_barrier (by intro t; exact Nat.zero_le _) read (by omega)

def site (p : Fin 7) : Nat := 3+p.val

theorem sites_injective : Function.Injective site := by
  intro p q h
  apply Fin.ext
  unfold site at h
  omega

/-- This one-word example has one active producer in plane zero. Values do
not appear in the ownership contract. -/
theorem plane_coverage (word : Word) : PlaneStores (result word).events 0 1 site := by
  intro index thread access observed write shared
  have member := List.mem_of_getElem? observed
  rw [event_history] at member
  simp only [history,List.mem_cons,List.not_mem_nil,or_false,Event.data.injEq,
    reduceCtorEq,false_or] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨0,by decide,rfl,rfl⟩
  all_goals contradiction

/-- Reprove the concrete read through derived producer ordering and plane
ownership. No `Across` or `SoleWriter` premise is supplied. -/
theorem derived_read (word : Word) (source : Nat → Fin 8 → Sources.Origin Nat)
    (compatible : Visibility.Compatible (fun _ _ => 0) (result word).events source)
    (performed : Visibility.Performed (result word).events source) : word=42 := by
  obtain ⟨w,wa,hw,pc,ordered,value,bytes⟩ := read_from_plane_producer (actual_run word) rfl forward
    (plane_coverage word) sites_injective 0
    (show program[site 0]?=some (.data (.store64 .shared (.offset 2 0) (.reg 8))) from rfl)
    stops_writer (by decide) (by decide) (show program[4]?=some (.sync 0) from rfl)
    stops_barrier (by intro t; exact Nat.zero_le _)
    (show (result word).events[5]?=some (.data 1 ⟨.shared,⟨5,false,0,word⟩⟩) from rfl)
    (by change 4<5; decide) rfl rfl rfl compatible performed
  have member := List.mem_of_getElem? hw
  rw [event_history] at member
  simp [history] at member
  rcases member with rfl | ⟨_,rfl⟩
  · exact value
  · simp [site] at pc

end PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks
