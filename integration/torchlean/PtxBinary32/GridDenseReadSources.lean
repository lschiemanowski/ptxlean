import PtxBinary32.GridDenseWriter
import PtxBinary32.GridDenseCoverage
import PtxBinary32.GridDenseGlobalReads

/-! Read values are forced by the actual combined graph, private-cell ownership,
and actual group barrier events. Desired producer values are not premises. -/
namespace Ptx.Scalar.Parallel.GridDense
open Ptx.Scalar.Parallel.Dense
open Ptx.TraceMemory (Access AccessKind)

def Admitted (s : Dense.Shape) (global : List Word) (seeds : Fin s.threads → Scalar.State)
    (events : List (Grid.Event s.rows s.width))
    (source : Fin (Grid.Memory.labels (program s) (initial s global seeds) events).length → Fin (Grid.Memory.labels (program s) (initial s global seeds) events).length)
    (co : Fin (Grid.Memory.labels (program s) (initial s global seeds) events).length → Fin (Grid.Memory.labels (program s) (initial s global seeds) events).length → Bool) : Prop :=
  Graph.Ordered.Valid (Grid.Memory.graph (program s) (initial s global seeds) events source co)
    (Grid.Memory.cross (program s) (initial s global seeds) events)

theorem visible_store (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (source co) (valid : Admitted s global seeds events source co)
    (g : Fin s.rows) (phase : Phase events g) (p q : Nat) (writer reader : Fin s.width)
    (storeOcc loadOcc : Scalar.Occurrence) (stored loaded : MemoryEffect)
    (atP : events[p]?=some (g,.scalar writer (some .shared) storeOcc))
    (atQ : events[q]?=some (g,.scalar reader (some .shared) loadOcc))
    (sm : storeOcc.memory=some stored) (lm : loadOcc.memory=some loaded)
    (sk : stored.kind=.store) (lk : loaded.kind=.load) (same : stored.address=loaded.address)
    (earlier : storeOcc.pc<phase.key.site) (later : phase.key.site<loadOcc.pc) :
    loaded.value=stored.value ∧ p<q := by
  obtain ⟨w,wl⟩ := Grid.Memory.graph_complete run source co p g writer .shared storeOcc stored atP sm
  obtain ⟨r,rl⟩ := Grid.Memory.graph_complete run source co q g reader .shared loadOcc loaded atQ lm
  let graph := Grid.Memory.graph (program s) (initial s global seeds) events source co
  have written : graph.write w := by simp [graph,Graph.write,wl,Grid.Memory.ofEffect,Access.effect,AccessKind.op,sk]
  have read : graph.read r := by simp [graph,Graph.read,rl,Grid.Memory.ofEffect,Access.effect,AccessKind.op,lk]
  have noninitial : ¬graph.initial w := by simp [graph,Graph.initial,wl,Grid.Memory.ofEffect,Access.effect,AccessKind.op,sk]
  have address : graph.sameAddress w r := by simp [graph,Graph.sameAddress,wl,rl,Grid.Memory.ofEffect,Access.effect,same]
  obtain ⟨arrival,ac,atA⟩ := Grid.completed_arrival run (program_straight s) (fun _ => rfl) g phase.position phase.key phase.observed writer
  have before := (Grid.Control.position_iff_pc run (program_straight s) p arrival _ _ (g,writer) storeOcc.pc phase.key.site atP atA rfl rfl).mpr earlier
  have after := Grid.Control.site_after_completion run (program_straight s) (initial_aligned s global seeds) phase.position q phase.key _ g reader loadOcc.pc phase.observed atQ rfl later
  have wl' := wl
  have rl' := rl
  change (Grid.Memory.labels (program s) (initial s global seeds) events)[w]=_ at wl'
  change (Grid.Memory.labels (program s) (initial s global seeds) events)[r]=_ at rl'
  have edge : Grid.Memory.cross (program s) (initial s global seeds) events w r := by
    exact ⟨g,writer,reader,phase.key,arrival,phase.position,atA,phase.observed,ac,
      by simp [wl'],by simp [rl'],by simpa [wl'] using before,by simpa [rl'] using after⟩
  have latest : ∀ v, graph.write v → graph.sameAddress v r → v≠w → graph.coherence v w := by
    intro v hv sameVR ne
    have init : graph.initial v := by
      by_contra no
      exact ne (graph_writer_unique s b global seeds run source co v w hv written no noninitial (sameVR.trans address.symm))
    exact valid.co.initFirst v w init written (sameVR.trans address.symm) ne
  have result := Graph.Ordered.value_of_latest graph _ valid w r written read address
    (Graph.Ordered.extra_cause graph _ w r edge address) latest
  exact ⟨by simpa [graph,wl,rl,Grid.Memory.ofEffect,Access.effect] using result,by omega⟩

theorem plane_publication (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (halted : ∀ g t, ((final.blocks g).lanes t).halted=true) (g : Fin s.rows) (plane : Nat) (hp : plane≤s.depth) :
    ∃ phase : Phase events g, phase.key.site=sharedStorePC plane+1 ∧ ∀ t,
      (thread s g t).val%s.width<2^(s.depth-plane) →
      ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect),
        events[p]?=some (g,.scalar t (some .shared) occ) ∧ occ.pc=sharedStorePC plane ∧
        occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer (plane*s.threads+(thread s g t).val) := by
  let first : Fin s.width := ⟨0,width_positive s⟩
  have phases := completed_phases s b global seeds run g first (halted g first)
  cases plane with
  | zero =>
    obtain ⟨phase,site⟩ := phases.1
    refine ⟨phase,by simpa [sharedStorePC] using site,?_⟩
    intro t _
    obtain ⟨p,occ,effect,atP,pc,memory,kind,addr⟩ := completed_product_store s b global seeds run g t (halted g t)
    exact ⟨p,occ,effect,atP,by simpa [sharedStorePC] using pc,memory,kind,by simpa using addr⟩
  | succ k =>
    obtain ⟨phase,site⟩ := phases.2 k hp
    refine ⟨phase,by simpa [sharedStorePC] using site,?_⟩
    intro t active
    obtain ⟨p,occ,effect,atP,pc,memory,kind,addr⟩ := completed_round_store s b global seeds run g t (halted g t) k hp active
    exact ⟨p,occ,effect,atP,by simpa [sharedStorePC] using pc,memory,kind,by simpa [nextIndex,Nat.add_comm] using addr⟩

/-- Both children stay in the same row group; no cross-group barrier is needed. -/
theorem child_owner (s : Dense.Shape) (g : Fin s.rows) (k : Nat) (hk : k<s.depth) (t : Fin s.width) (right : Bool)
    (active : (thread s g t).val%s.width<2^(s.depth-(k+1))) :
    ∃ u : Fin s.width, (thread s g u).val%s.width<2^(s.depth-k) ∧
      k*s.threads+(thread s g u).val=leftIndex s k (thread s g t)+(if right then 1 else 0) := by
  have children := children_bound s k t.val hk (by simpa [(thread_coordinates s g t).2] using active)
  have width : 2^(s.depth-k)≤s.width := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  let c := 2*t.val+(if right then 1 else 0)
  have hc : c<2^(s.depth-k) := by cases right <;> dsimp [c] <;> omega
  let u : Fin s.width := ⟨c,lt_of_lt_of_le hc width⟩
  refine ⟨u,by simpa [(thread_coordinates s g u).2] using hc,?_⟩
  have coords := (coordinates s (thread s g u)).2.2
  rw [(thread_coordinates s g u).1,(thread_coordinates s g u).2] at coords
  rw [← coords]
  have tc := (coordinates s (thread s g t)).2.2
  rw [(thread_coordinates s g t).1,(thread_coordinates s g t).2] at tc
  simp only [leftIndex,Shape.thread,(thread_coordinates s g t).2,u,c] at tc ⊢
  omega

/-- Every actual shared load in a completed admitted run observes an earlier
actual producer store. Its address, active owner and phase are all derived. -/
theorem shared_read_source (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (halted : ∀ g t, ((final.blocks g).lanes t).halted=true) (source co) (valid : Admitted s global seeds events source co)
    (q : Nat) (g : Fin s.rows) (reader : Fin s.width) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atQ : events[q]?=some (g,.scalar reader (some .shared) occ))
    (memory : occ.memory=some effect) (load : effect.kind=.load) :
    ∃ (p : Nat) (writer : Fin s.width) (storeOcc : Scalar.Occurrence) (stored : MemoryEffect),
      events[p]?=some (g,.scalar writer (some .shared) storeOcc) ∧ storeOcc.memory=some stored ∧
      stored.kind=.store ∧ stored.address=effect.address ∧ effect.value=stored.value ∧ p<q := by
  rcases candidate_load_address s b global seeds run g reader .shared occ effect (List.mem_of_getElem? atQ) memory load with
    ⟨weight,site,sp,_,_⟩ | ⟨k,hk,right,site,_,active,addr⟩ | ⟨bias,site,sp,leader,addr⟩
  · cases sp
  · obtain ⟨writer,wa,index⟩ := child_owner s g k hk reader right active
    obtain ⟨phase,barrierSite,producers⟩ := plane_publication s b global seeds run halted g k (by omega)
    obtain ⟨p,so,stored,atP,pc,sm,sk,sa⟩ := producers writer wa
    have same : stored.address=effect.address := by rw [sa,addr,index]
    have before : so.pc<phase.key.site := by omega
    have after : phase.key.site<occ.pc := by
      rw [barrierSite,site]
      cases k <;> cases right <;> simp [sharedStorePC] <;> omega
    have observed := visible_store s b global seeds run source co valid g phase p q writer reader so occ stored effect
      atP atQ sm memory sk load same before after
    exact ⟨p,writer,so,stored,atP,sm,sk,same,observed⟩
  · cases bias with
    | true => cases sp
    | false =>
      obtain ⟨phase,barrierSite,producers⟩ := plane_publication s b global seeds run halted g s.depth (Nat.le_refl _)
      obtain ⟨p,so,stored,atP,pc,sm,sk,sa⟩ := producers reader (by simp [leader])
      have same : stored.address=effect.address := by rw [sa,addr]; simp [rootIndex,Nat.add_comm]
      have before : so.pc<phase.key.site := by omega
      have after : phase.key.site<occ.pc := by
        rw [barrierSite,site]
        cases h : s.depth <;> simp [sharedStorePC]
        omega
      have observed := visible_store s b global seeds run source co valid g phase p q reader reader so occ stored effect
        atP atQ sm memory sk load same before after
      exact ⟨p,reader,so,stored,atP,sm,sk,same,observed⟩

end Ptx.Scalar.Parallel.GridDense
