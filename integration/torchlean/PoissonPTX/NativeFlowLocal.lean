import PoissonPTX.NativeFlow
import PoissonPTX.ConcurrentLocalBlock

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

theorem update_self (s : State n) (thread : Fin n) : update s thread (lane s thread)=s := by
  cases s
  simp [update,lane,setLane]

theorem update_twice (s : State n) (thread : Fin n) (first second : Flow.State) :
    update (update s thread first) thread second=update s thread second := by
  simp [update,setLane]

/-- Embed an actual scalar observed run in one native thread, retaining all
word and index records. Other lanes and the barrier state remain unchanged. -/
theorem lift_local {start : State n}
    (run : Flow.Observed.Runs (ctx thread) code (lane start thread) words indices final)
    (fresh : start.core.barrier.arrived thread=false)
    (fetch : ∀ (pc : Nat) (i : Flow.Instr), code[pc]?=some i → program[pc]?=some (.flow i)) :
    Runs cfg ctx program start (words.map (Event.data thread)) (indices.map (thread,·)) (update start thread final) := by
  generalize eq : lane start thread=localStart at run
  induction run generalizing start with
  | nil => rw [← eq,update_self]; exact .nil
  | @cons s next access index words indices final step rest ih =>
    obtain ⟨running,i,found,effect⟩ := step
    let middle := update start thread next
    have one : Step cfg ctx program thread start
        ⟨middle,access.toList.map (Event.data thread),index.toList.map (thread,·)⟩ := by
      apply Step.flow (by simpa only [← eq,lane] using running) fresh
      · have actual := fetch _ _ found
        simpa only [← eq,lane] using actual
      · simpa only [eq] using effect
    have second := ih (start:=middle) fresh (lane_update_self _ _ _)
    simpa only [List.map_append,middle,update_twice] using Runs.cons one second

/-- Embed a straight-line block of actual candidate data effects. Candidate
load words are retained; admission is deliberately proved on the joined trace. -/
theorem lift_block {start : State n}
    (run : Local.Block code (start.core.lanes thread) words final)
    (fresh : start.core.barrier.arrived thread=false) (running : start.halted thread=false)
    (fetch : ∀ j op, code[j]?=some op → program[(start.core.lanes thread).pc+j]?=some (.flow (.data (.data op)))) :
    Runs cfg ctx program start (words.map (Event.data thread)) []
      (update start thread {(lane start thread) with core:=final}) := by
  generalize eq : start.core.lanes thread=localStart at run
  induction run generalizing start with
  | @nil s =>
    have same : {lane start thread with core:=s}=lane start thread := by rw [← eq]; rfl
    rw [same,update_self]; exact .nil
  | @cons op s next access rest words final step tail ih =>
    let middle := update start thread {(lane start thread) with core:=next}
    have one : Step cfg ctx program thread start ⟨middle,access.toList.map (Event.data thread),[]⟩ := by
      apply Step.flow (index:=none) running fresh
      · simpa using fetch 0 op (by simp)
      · exact .data (.data (by simpa only [eq,lane] using step))
    have nextFetch : ∀ j op, rest[j]?=some op → program[(middle.core.lanes thread).pc+j]?=some (.flow (.data (.data op))) := by
      intro j op found
      have actual := fetch (j+1) op (by simpa using found)
      simpa only [middle,update,setLane,Function.update_self,eq,data_pc step,Nat.add_assoc,Nat.add_comm 1 j] using actual
    have second := ih (start:=middle) fresh (by simp [middle,update,lane,running]) nextFetch (by simp [middle,update,setLane])
    have target : update middle thread {lane middle thread with core:=final}=
        update start thread {lane start thread with core:=final} := by simp [middle,lane_update_self,update_twice]
    simpa only [List.map_append,target,List.nil_append] using Runs.cons one second

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
