import PtxBinary32.GridDenseOwnership
import PtxBinary32.GridCoverage
import PtxBinary32.GridBarrierOrder
import PtxBinary32.DenseCoverage

/-! Completed row-group executions contain actual product/round/output stores
and actual group barriers. These are consequences, not admission premises. -/
namespace Ptx.Scalar.Parallel.GridDense
open Ptx.Scalar.Parallel.Dense

structure Phase (events : List (Grid.Event groups n)) (g : Fin groups) where
  position : Nat
  key : Barrier.Key
  observed : events[position]?=some (g,.barrier (.completion key))

/-- Halting entails a fetched exit after the entire forward instruction list. -/
theorem completed_pc_bound (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (halted : ((final.blocks g).lanes t).halted=true) :
    22+16*s.depth+19≤((final.blocks g).lanes t).scalar.pc := by
  obtain ⟨pc,fetch,member⟩ := Grid.Control.halted_exit_origin run (Dense.Compact.program_straight s) g t rfl halted
  obtain ⟨p,hp,atP⟩ := List.mem_iff_getElem.mp member
  have bound := ((Grid.Control.runs_progress run (Dense.Compact.program_straight s)).emitted p (g,.exit t pc) (g,t) pc
    (by simpa [hp] using atP) rfl).2
  have upper := (Grid.Control.cursor_bounds final (g,t)).2
  have site := Dense.Compact.fetched_exit_site s pc fetch
  dsimp only at upper
  omega

/-- Every passed barrier site has an actual completion in this same trace. -/
theorem completed_barrier_exists (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (halted : ((final.blocks g).lanes t).halted=true)
    (pc : Nat) (earlier : pc<22+16*s.depth+19) (fetch : (Dense.Compact.program s)[pc]?=some (.sync 0)) :
    ∃ (c : Nat) (key : Barrier.Key), events[c]?=some (g,.barrier (.completion key)) ∧ key.site=pc :=
  Grid.Control.crossed_barrier_exists run (Dense.Compact.program_straight s) (initial_aligned s global seeds) g t pc (Nat.zero_le _)
    (lt_of_lt_of_le earlier (completed_pc_bound s b global seeds run g t halted)) fetch

/-- One exited participant entails all preceding collective completions, each
with the actual per-thread arrivals supplied by the machine's history theorem. -/
theorem completed_phases (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (halted : ((final.blocks g).lanes t).halted=true) :
    (∃ phase : Phase events g, phase.key.site=21) ∧
    (∀ k, k<s.depth → ∃ phase : Phase events g, phase.key.site=22+16*k+15) := by
  constructor
  · obtain ⟨c,key,hc,site⟩ := completed_barrier_exists s b global seeds run g t halted 21 (by omega) (by
      simp [Dense.Compact.program,Dense.Compact.products,pointer,scalar,guarded])
    exact ⟨⟨c,key,hc⟩,site⟩
  · intro k hk
    obtain ⟨c,key,hc,site⟩ := completed_barrier_exists s b global seeds run g t halted (22+16*k+15) (by omega) (by
      rw [Dense.Compact.round_fetch s k hk 15 (by simp)]; exact Dense.Compact.round_barrier s k)
    exact ⟨⟨c,key,hc⟩,site⟩

private theorem completed_store_exists (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (halted : ((final.blocks g).lanes t).halted=true)
    (pc : Nat) (space : Space) (guard : Scalar.Guard) (addr : Scalar.Operand64) (value : Scalar.Operand32)
    (earlier : pc<22+16*s.depth+19)
    (fetch : (Dense.Compact.program s)[pc]?=some (.memory space ⟨guard,.store addr value⟩))
    (enabled : guard=.always ∨ guard=.pred 0 true ∧ (AddressControl.atPC (Dense.Compact.program s) (controlSeed s seeds (thread s g t)) pc).preds 0=true) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (g,.scalar t (some space) occ) ∧ occ.pc=pc ∧
      occ.memory=some effect ∧ effect.kind=.store := by
  have finish := completed_pc_bound s b global seeds run g t halted
  obtain ⟨before,after,middle,out,u,candidate,trace,frontRun,step,_,old,new⟩ :=
    Grid.Control.crossing_step run (Dense.Compact.program_straight s) g t pc (Nat.zero_le _) (by omega)
  obtain ⟨owner,next,occ,ev,emitted⟩ := Control.memory_crossing (t := t) (space := space) (i := ⟨guard,.store addr value⟩) step (Dense.Compact.program_straight s)
    ((Grid.runs_aligned frontRun (initial_aligned s global seeds)) g) (by simpa [Grid.view,old] using fetch) (by simpa [Grid.view,old] using new)
  subst u
  have projected := candidate_control s b global seeds frontRun g t
  dsimp only [Grid.view] at projected
  have active : guard.eval {((middle.blocks g).lanes t).scalar with memory := arena (Grid.view middle g) (some space)}=true := by
    rcases enabled with rfl | ⟨rfl,active⟩
    · rfl
    · simpa [Scalar.Guard.eval,projected.pred,old] using active
  dsimp only [Grid.view] at ev active
  simp only [Scalar.eval,active,↓reduceIte] at ev
  split at ev
  · contradiction
  · have info : occ.pc=((middle.blocks g).lanes t).scalar.pc ∧ ∃ effect : MemoryEffect,
        occ.memory=some effect ∧ effect.kind=.store := by
      obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj ev
      exact ⟨rfl,⟨.store,addr.eval ((middle.blocks g).lanes t).scalar,value.eval ((middle.blocks g).lanes t).scalar⟩,rfl,rfl⟩
    obtain ⟨site,effect,memory,kind⟩ := info
    exact ⟨before.length,occ,effect,by simp [trace,emitted,Grid.tag],site.trans old,memory,kind⟩

/-- Every exited thread emitted its unconditional product publication. -/
theorem completed_product_store (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (halted : ((final.blocks g).lanes t).halted=true) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (g,.scalar t (some .shared) occ) ∧ occ.pc=20 ∧
      occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer ((thread s g t).val%s.width) := by
  obtain ⟨p,occ,effect,atP,pc,memory,store⟩ := completed_store_exists s b global seeds run g t halted
    20 .shared .always (.reg 2) (.reg 6) (by omega) (by simp [Dense.Compact.program,Dense.Compact.products,pointer,scalar,guarded,Scalar.Instr.plain]) (.inl rfl)
  refine ⟨p,occ,effect,atP,pc,memory,store,?_⟩
  rcases candidate_store_address s b global seeds run g t .shared occ effect (List.mem_of_getElem? atP) memory store with h | ⟨k,hk,site,_,_⟩ | ⟨site,_,_⟩
  · exact h.2.2
  · omega
  · omega

/-- An active column emitted its store in every preceding reduction round. -/
theorem completed_round_store (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (halted : ((final.blocks g).lanes t).halted=true) (k : Nat) (hk : k<s.depth)
    (active : (thread s g t).val%s.width<2^(s.depth-(k+1))) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (g,.scalar t (some .shared) occ) ∧ occ.pc=22+16*k+14 ∧
      occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer (Dense.Compact.nextIndex s k (thread s g t)) := by
  obtain ⟨p,occ,effect,atP,pc,memory,store⟩ := completed_store_exists s b global seeds run g t halted
    (22+16*k+14) .shared (.pred 0 true) (.reg 2) (.reg 6) (by omega)
    (by rw [Dense.Compact.round_fetch s k hk 14 (by simp)]; rfl)
    (.inr ⟨rfl,by rw [Dense.Compact.round_control_active s b.arithmetic seeds (thread s g t) k hk]; simp [active]⟩)
  refine ⟨p,occ,effect,atP,pc,memory,store,?_⟩
  rcases candidate_store_address s b global seeds run g t .shared occ effect (List.mem_of_getElem? atP) memory store with ⟨site,_,_⟩ | ⟨j,hj,site,_,addr⟩ | ⟨site,_,_⟩
  · omega
  · have eq : j=k := by omega
    simpa [eq] using addr
  · omega

/-- Each exited row leader emitted the row's global output store. -/
theorem completed_output_store (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (Dense.Compact.program s) (initial s global seeds) events final)
    (g : Fin s.rows) (t : Fin s.width) (halted : ((final.blocks g).lanes t).halted=true) (leader : (thread s g t).val%s.width=0) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (g,.scalar t (some .global) occ) ∧ occ.pc=22+16*s.depth+18 ∧
      occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer (outputIndex s (thread s g t)) := by
  obtain ⟨p,occ,effect,atP,pc,memory,store⟩ := completed_store_exists s b global seeds run g t halted
    (22+16*s.depth+18) .global (.pred 0 true) (.reg 6) (.reg 6) (by omega)
    (by rw [Dense.Compact.output_fetch s 18 (by simp)]; rfl)
    (.inr ⟨rfl,by rw [(Dense.Compact.output_control_address s b.arithmetic seeds (thread s g t)).2]; simp [leader]⟩)
  exact ⟨p,occ,effect,atP,pc,memory,store,
    (candidate_global_owner s b global seeds run g t occ effect (List.mem_of_getElem? atP) memory store).2.1⟩

end Ptx.Scalar.Parallel.GridDense
