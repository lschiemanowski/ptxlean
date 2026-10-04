import PoissonPTX.CellWitnessFront
import PoissonPTX.ByteHistoryFrame

namespace PtxTorchLean.Poisson.PTX.Concurrent.WithTail

def noLoad : Kernel.Instr → Bool
  | .data (.load64 ..) => false
  | _ => true

theorem access_writes (safe : noLoad i=true) (observed : access i s next=some a) : a.data.store=true := by
  cases i <;> simp only [access] at observed <;> try cases observed
  case data op =>
    cases op <;> try cases observed
    case load64 => simp [noLoad] at safe
    case store64 => rfl

/-- Embed a finite actual tail execution, retaining all its real stores and
returns. Fetches use the original global PC and tail offset. -/
theorem tail_exec_lift {start : State n}
    (execution : Kernel.Exec (ctx thread) code (lane start thread) final)
    (fresh : start.core.barrier.arrived thread=false)
    (past : front.length≤(start.core.lanes thread).pc)
    (fetch : ∀ j i, code[j]?=some i → tail[(start.core.lanes thread).pc-front.length+j]?=some i)
    (safe : ∀ i∈code, noLoad i=true) :
    ∃ events, Runs cfg ctx front tail start events (update start thread final) ∧
      ∀ owner a, Event.data owner a∈events → a.data.store=true := by
  generalize laneEq : lane start thread=localStart at execution
  induction execution generalizing start with
  | @stop i localStart final code running actual stopped =>
    have step : Step cfg ctx front tail thread start
        ⟨update start thread final,(access i (lane start thread) final).toList.map (Event.data thread)⟩ := by
      exact .tail (by simpa only [← laneEq,lane] using running) fresh past (by simpa using fetch 0 i (by simp)) (laneEq ▸ actual)
    refine ⟨_,.cons step .nil,?_⟩
    intro owner a member
    have selected : access i (lane start thread) final=some a ∧ thread=owner := by simpa using member
    exact access_writes (safe i (by simp)) selected.1
  | @next i localStart middle code final running actual continues rest ih =>
    let next := update start thread middle
    have step : Step cfg ctx front tail thread start
        ⟨next,(access i (lane start thread) middle).toList.map (Event.data thread)⟩ := by
      exact .tail (by simpa only [← laneEq,lane] using running) fresh past (by simpa using fetch 0 i (by simp)) (laneEq ▸ actual)
    have nextLane : lane next thread=middle := by simp [next,lane,update,setLane]
    have nextPC : (next.core.lanes thread).pc=(start.core.lanes thread).pc+1 := by
      have position := Kernel.eval_pc actual
      simpa [next,update,setLane,← laneEq,lane] using position
    have laterFetch : ∀ j item, code[j]?=some item →
        tail[(next.core.lanes thread).pc-front.length+j]?=some item := by
      intro j item found
      have before := fetch (j+1) item (by simpa using found)
      rw [nextPC, show (start.core.lanes thread).pc+1-front.length+j =
        (start.core.lanes thread).pc-front.length+(j+1) by omega]
      exact before
    obtain ⟨events,run,writes⟩ := ih (start:=next) fresh (by rw [nextPC]; omega) laterFetch
      (fun i member => safe i (by simp [member])) nextLane
    refine ⟨(access i (lane start thread) middle).toList.map (Event.data thread)++events,?_,?_⟩
    · have same : update next thread final=update start thread final := by simp [next,update,setLane]
      rw [same] at run
      exact .cons step run
    · intro owner a member
      rcases List.mem_append.mp member with first | later
      · have selected : access i (lane start thread) middle=some a ∧ thread=owner := by simpa using first
        exact access_writes (safe i (by simp)) selected.1
      · exact writes owner a later

end PtxTorchLean.Poisson.PTX.Concurrent.WithTail
