import PoissonPTX.ConcurrentExec

/-! Straight-line local candidate execution and its embedding into one thread
of the concurrent machine. Arbitrary load choices still need source admission. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Local

inductive Block : List Op → PTX.State → List Access → PTX.State → Prop where
  | nil : Block [] s [] s
  | cons : Data op s next access → Block rest next events final →
      Block (op::rest) s (access.toList++events) final

theorem pc (run : Block code start events final) : final.pc=start.pc+code.length := by
  induction run with
  | nil => simp
  | cons step _ ih => rw [ih,data_pc step]; simp; omega

/-- Other threads and barrier state are unchanged while this local block runs. -/
theorem lift {start : State n} {thread : Fin n} (run : Block code (start.lanes thread) events final)
    (fresh : start.barrier.arrived thread=false)
    (fetch : ∀ (j : Nat) (op : Op), code[j]?=some op →
      program[(start.lanes thread).pc+j]?=some (.data op)) :
    Runs cfg program start (events.map (Event.data thread)) (setLane start thread final) := by
  generalize eq : start.lanes thread = localStart at run
  induction run generalizing start with
  | @nil laneStart =>
    have same : setLane start thread laneStart=start := by
      cases start; simp_all [setLane]
    rw [same]; exact .nil
  | @cons op s next access rest events final step tail ih =>
    let middle := setLane start thread next
    have one : Step cfg program thread start
        ⟨middle,access.toList.map (Event.data thread)⟩ := by
      refine ⟨fresh,.data op,?_,?_⟩
      · simpa using fetch 0 op (by simp)
      · exact Dispatch.data (by simpa only [eq] using step)
    have restFetch : ∀ j op, rest[j]?=some op → program[(middle.lanes thread).pc+j]?=some (.data op) := by
      intro j item found
      have h := fetch (j+1) item (by simpa using found)
      simpa only [middle,setLane,Function.update_self,eq,data_pc step,Nat.add_assoc,Nat.add_comm 1 j] using h
    have second := ih (start:=middle) fresh restFetch (by simp [middle,setLane])
    have same : setLane middle thread final=setLane start thread final := by
      simp [middle,setLane]
    simpa only [same,List.map_append] using runs_append (by simpa using Runs.cons one Runs.nil) second

end PtxTorchLean.Poisson.PTX.Concurrent.Local
