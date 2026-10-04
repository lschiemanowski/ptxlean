import PoissonPTX.CellEntrySerial
import PoissonPTX.ConcurrentBarrier

namespace PtxTorchLean.Poisson.PTX.CellEntry
open Ptx

def afterRound (s : State n) (generation : Nat) : State n :=
  {s with core:=Concurrent.afterRound s.core generation}

def roundPrefix (s : State n) (pc generation count : Nat) : State n :=
  if count=n then afterRound s generation else
    {s with core:={s.core with barrier := Barrier.prefixState generation count,site := if count=0 then none else some pc}}

theorem prefix_dispatch (cfg : Concurrent.Config n) (s : State n) (program : List Instr)
    (pc generation count : Nat) (bound : count<n)
    (pcs : ∀ t, (s.core.lanes t).pc=pc) (fetch : program[pc]?=some (.sync)) :
    ∃ out, Step cfg ctx program ⟨count,bound⟩ (roundPrefix s pc generation count) out ∧
      out.indices=[] ∧ out.state=roundPrefix s pc generation (count+1) ∧
      ∀ e∈out.events, ∃ b, e=.barrier b := by
  let t : Fin n := ⟨count,bound⟩
  let c : Barrier.Config n := ⟨cfg.cta,0,pc,cfg.nonempty⟩
  let r : Barrier.Request n := ⟨⟨cfg.cta,0,generation,pc⟩,t⟩
  let start := roundPrefix s pc generation count
  have ne : count≠n := by omega
  have hc : Concurrent.barrierConfig cfg start.core t=c := by
    simp [Concurrent.barrierConfig,start,roundPrefix,ne,pcs,c]; split <;> rfl
  have hr : Concurrent.barrierRequest cfg start.core t 0=r := by
    simp [Concurrent.barrierRequest,start,roundPrefix,ne,pcs,r,Barrier.prefixState]
  have hb : start.core.barrier=Barrier.prefixState generation count := by simp [start,roundPrefix,ne]
  have fresh : Barrier.Runnable (Barrier.prefixState generation count) t := by
    simp [Barrier.Runnable,Barrier.prefixState,t]
  have same : r.key=Barrier.key c (Barrier.prefixState generation count) := rfl
  have marked : Barrier.mark (Barrier.prefixState generation count) r.thread=Barrier.prefixState generation (count+1) :=
    Barrier.mark_prefix generation count bound
  refine ⟨⟨{start with core:=(Concurrent.synchronize cfg start.core t 0).state},(Concurrent.synchronize cfg start.core t 0).events,[]⟩,?_,rfl,?_,?_⟩
  · refine ⟨?_,.sync,?_,Dispatch.sync⟩
    · simpa [start,roundPrefix,ne,Barrier.Runnable,t] using fresh
    · simpa [start,roundPrefix,ne,pcs] using fetch
  · by_cases last : count+1=n
    · have complete : Barrier.Complete (Barrier.mark (Barrier.prefixState generation count) r.thread) := by
        rw [marked,Barrier.complete_prefix_iff c]; omega
      have h := Barrier.completing_step c (Barrier.prefixState generation count) r same fresh complete
      simp only [Concurrent.synchronize,hc,hr,hb,h]
      simp [start,roundPrefix,ne,last,afterRound,Concurrent.afterRound,Barrier.prefixState]
    · have incomplete : ¬Barrier.Complete (Barrier.mark (Barrier.prefixState generation count) r.thread) := by
        rw [marked,Barrier.complete_prefix_iff c]; omega
      have h := Barrier.waiting_step c (Barrier.prefixState generation count) r same fresh incomplete
      simp only [Concurrent.synchronize,hc,hr,hb,h]
      simp [start,roundPrefix,ne,last,marked,c]

  · intro e member
    simp only [Concurrent.synchronize] at member
    split at member
    · simp at member
    · obtain ⟨b,found,rfl⟩ := List.mem_map.mp member; exact ⟨b,rfl⟩
    · obtain ⟨b,found,rfl⟩ := List.mem_map.mp member; exact ⟨b,rfl⟩

/-- The witness includes every participant, independently of matrix activity. -/
theorem barrier_round_exists (cfg : Concurrent.Config n) (s : State n) (program : List Instr)
    (pc generation : Nat) (pcs : ∀ t, (s.core.lanes t).pc=pc)
    (reset : s.core.barrier=Barrier.reset generation) (site : s.core.site=none)
    (fetch : program[pc]?=some (.sync)) :
    ∃ events, Runs cfg ctx program s events [] (afterRound s generation) ∧
      ∀ e∈events, ∃ b, e=.barrier b := by
  have base : roundPrefix s pc generation 0=s := by
    have ne : 0≠n := by have := cfg.nonempty; omega
    simp [roundPrefix,ne,Barrier.prefix_zero,← reset,← site]
  have witness : ∀ count, count≤n → ∃ events, Runs cfg ctx program s events [] (roundPrefix s pc generation count) ∧
      ∀ e∈events, ∃ b, e=.barrier b := by
    intro count bound
    induction count with
    | zero => exact ⟨[],by rw [base]; exact Runs.nil,by simp⟩
    | succ count ih =>
      obtain ⟨events,run,good⟩ := ih (by omega)
      obtain ⟨out,step,noIndices,next,stepGood⟩ := prefix_dispatch cfg s program pc generation count (by omega) pcs fetch
      have one : Runs cfg ctx program (roundPrefix s pc generation count) out.events [] (roundPrefix s pc generation (count+1)) := by
        simpa only [List.append_nil,noIndices,next] using Runs.cons step (Runs.nil (s:=out.state))
      refine ⟨events++out.events,by simpa using Serial.append run one,?_⟩
      intro e member
      rcases List.mem_append.mp member with earlier | later
      · exact good e earlier
      · exact stepGood e later
  simpa [roundPrefix] using witness n (Nat.le_refl n)


end PtxTorchLean.Poisson.PTX.CellEntry
