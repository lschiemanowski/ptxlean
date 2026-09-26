import PtxBinary32.DenseCoverage
import PtxBinary32.DenseLoadSites
import PtxBinary32.ParallelVisibility
import PtxBinary32.ParallelChronology

/-! Read sources follow from actual addresses, producer existence, barriers and
admission. No selected read word or desired arithmetic value is assumed. -/
namespace Ptx.Scalar.Parallel.Dense
open Ptx.TraceMemory

/-- The existing memory constraints with order recovered from this exact run. -/
def Admitted (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final) (source : Fin (Memory.labels (program s) global shared events).length → Fin (Memory.labels (program s) global shared events).length)
    (co : Fin (Memory.labels (program s) global shared events).length → Fin (Memory.labels (program s) global shared events).length → Bool) : Prop :=
  Graph.Ordered.Valid (Memory.graph (program s) global shared events source co)
    (Memory.runOrder run rfl source co).cross

/-- A same-location store before a completed phase supplies the later load.
The kernel's proved ownership discharges the unique-writer premise. -/
theorem visible_store (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (source co) (valid : Admitted s b global shared seeds run source co)
    (phase : History.Phase events) (p q : Nat) (writer reader : Fin s.threads)
    (space : Space) (storeOcc loadOcc : Scalar.Occurrence) (stored loaded : MemoryEffect)
    (atP : events[p]?=some (.scalar writer (some space) storeOcc))
    (atQ : events[q]?=some (.scalar reader (some space) loadOcc))
    (sm : storeOcc.memory=some stored) (lm : loadOcc.memory=some loaded)
    (sk : stored.kind=.store) (lk : loaded.kind=.load) (same : stored.address=loaded.address)
    (earlier : storeOcc.pc<phase.key.site) (later : phase.key.site<loadOcc.pc) :
    loaded.value=stored.value ∧ p<q := by
  obtain ⟨w,wl⟩ := Memory.run_graph_complete run source co p writer space storeOcc stored atP sm
  obtain ⟨r,rl⟩ := Memory.run_graph_complete run source co q reader space loadOcc loaded atQ lm
  dsimp [initial] at wl rl
  have written : (Memory.graph (program s) global shared events source co).write w := by
    simp [Graph.write,wl,Memory.ofEffect,Access.effect,AccessKind.op,sk]
  have read : (Memory.graph (program s) global shared events source co).read r := by
    simp [Graph.read,rl,Memory.ofEffect,Access.effect,AccessKind.op,lk]
  have noninitial : ¬(Memory.graph (program s) global shared events source co).initial w := by
    simp [Graph.initial,wl,Memory.ofEffect,Access.effect,AccessKind.op,sk]
  have address : (Memory.graph (program s) global shared events source co).sameAddress w r := by
    simp [Graph.sameAddress,wl,rl,Memory.ofEffect,Access.effect,same]
  have forced := Memory.run_read_from_unique_writer_sites run rfl (program_straight s) source co phase w r writer reader valid
    (by simp [initial,wl,Memory.owner]) (by simp [initial,rl,Memory.owner]) ⟨some space,storeOcc,by simpa [initial,wl] using atP,earlier⟩
    ⟨some space,loadOcc,by simpa [initial,rl] using atQ,later⟩ written read address
    (by
      intro v hv sameVR nv
      exact graph_writer_unique s b global shared seeds run source co v w hv written nv noninitial
        (sameVR.trans address.symm))
  have arrival := History.arrival_position_spec (History.completed_arrivals run rfl) phase writer
  have before := scalar_before_arrival s run p _ writer _ storeOcc phase.key atP arrival.2 earlier
  have after := scalar_after_completion s run (reset_aligned _ _ _ _) phase.position q reader _ loadOcc phase.key phase.observed atQ later
  exact ⟨by simpa [initial,wl,rl,Memory.ofEffect,Access.effect] using forced.2,by omega⟩

/-- Plane zero contains products; positive planes contain the corresponding
completed reduction round. Only the represented active columns are producers. -/
theorem plane_publication (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (plane : Nat) (hp : plane≤s.depth) :
    ∃ phase : History.Phase events, phase.key.site=sharedStorePC plane+1 ∧ ∀ t,
      t.val%s.width<2^(s.depth-plane) →
      ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect),
        events[p]?=some (.scalar t (some .shared) occ) ∧ occ.pc=sharedStorePC plane ∧
        occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer (plane*s.threads+t.val) := by
  cases plane with
  | zero =>
    obtain ⟨phase,site,producers⟩ := completed_product_publication s b global shared seeds run halted
    refine ⟨phase,by simpa [sharedStorePC] using site,?_⟩
    intro t _
    obtain ⟨p,occ,effect,atP,pc,memory,kind,addr,_⟩ := producers t
    exact ⟨p,occ,effect,atP,by simpa [sharedStorePC] using pc,memory,kind,by simpa using addr⟩
  | succ k =>
    obtain ⟨phase,site,producers⟩ := completed_round_publication s b global shared seeds run halted k hp
    refine ⟨phase,by simpa [sharedStorePC] using site,?_⟩
    intro t active
    obtain ⟨p,occ,effect,atP,pc,memory,kind,addr,_⟩ := producers t active
    exact ⟨p,occ,effect,atP,by simpa [sharedStorePC] using pc,memory,kind,by simpa [nextIndex,Nat.add_comm] using addr⟩

/-- A reduction child is another active producer in the same row, in the
preceding plane. This arithmetic fact is independent of stored tensor values. -/
theorem child_owner (s : Shape) (k : Nat) (hk : k<s.depth) (t : Fin s.threads) (right : Bool)
    (active : t.val%s.width<2^(s.depth-(k+1))) :
    ∃ u : Fin s.threads, u.val%s.width<2^(s.depth-k) ∧
      k*s.threads+u.val=leftIndex s k t+(if right then 1 else 0) := by
  have children := children_bound s k (t.val%s.width) hk active
  have width : 2^(s.depth-k)≤s.width := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  let c := 2*(t.val%s.width)+(if right then 1 else 0)
  have hc : c<2^(s.depth-k) := by cases right <;> dsimp [c] <;> omega
  let u : Fin s.threads := ⟨s.thread (t.val/s.width) c,thread_bound s _ c (coordinates s t).1 (lt_of_lt_of_le hc width)⟩
  refine ⟨u,?_,?_⟩
  · simpa [u,Shape.thread,Nat.add_mod,Nat.mod_eq_of_lt (lt_of_lt_of_le hc width)] using hc
  · have coords := (coordinates s t).2.2
    dsimp [Shape.thread] at coords
    dsimp [u,c,Shape.thread,leftIndex]
    omega

/-- Every actual shared load in a completed admitted run observes an earlier
actual producer store. Its address, active owner and phase are all derived. -/
theorem shared_read_source (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (source co) (valid : Admitted s b global shared seeds run source co)
    (q : Nat) (reader : Fin s.threads) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atQ : events[q]?=some (.scalar reader (some .shared) occ))
    (memory : occ.memory=some effect) (load : effect.kind=.load) :
    ∃ (p : Nat) (writer : Fin s.threads) (storeOcc : Scalar.Occurrence) (stored : MemoryEffect),
      events[p]?=some (.scalar writer (some .shared) storeOcc) ∧ storeOcc.memory=some stored ∧
      stored.kind=.store ∧ stored.address=effect.address ∧ effect.value=stored.value ∧ p<q := by
  rcases candidate_load_address s b global shared seeds run reader .shared occ effect (List.mem_of_getElem? atQ) memory load with
    ⟨weight,site,sp,_,_⟩ | ⟨k,hk,right,site,_,active,addr⟩ | ⟨bias,site,sp,leader,addr⟩
  · cases sp
  · obtain ⟨writer,wa,index⟩ := child_owner s k hk reader right active
    obtain ⟨phase,barrierSite,producers⟩ := plane_publication s b global shared seeds run halted k (by omega)
    obtain ⟨p,so,stored,atP,pc,sm,sk,sa⟩ := producers writer wa
    have same : stored.address=effect.address := by rw [sa,addr,index]
    have before : so.pc<phase.key.site := by omega
    have after : phase.key.site<occ.pc := by
      rw [barrierSite,site]
      cases k <;> cases right <;> simp [sharedStorePC] <;> omega
    have observed := visible_store s b global shared seeds run source co valid phase p q writer reader .shared so occ stored effect
      atP atQ sm memory sk load same before after
    exact ⟨p,writer,so,stored,atP,sm,sk,same,observed⟩
  · cases bias with
    | true => cases sp
    | false =>
      obtain ⟨phase,barrierSite,producers⟩ := plane_publication s b global shared seeds run halted s.depth (Nat.le_refl _)
      obtain ⟨p,so,stored,atP,pc,sm,sk,sa⟩ := producers reader (by simp [leader])
      have same : stored.address=effect.address := by rw [sa,addr]; simp [rootIndex,Nat.add_comm]
      have before : so.pc<phase.key.site := by omega
      have after : phase.key.site<occ.pc := by
        rw [barrierSite,site]
        cases h : s.depth <;> simp [sharedStorePC]
        omega
      have observed := visible_store s b global shared seeds run source co valid phase p q reader reader .shared so occ stored effect
        atP atQ sm memory sk load same before after
      exact ⟨p,reader,so,stored,atP,sm,sk,same,observed⟩

end Ptx.Scalar.Parallel.Dense
