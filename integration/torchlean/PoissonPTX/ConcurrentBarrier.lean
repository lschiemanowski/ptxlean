import PoissonPTX.ConcurrentHistory

/-! Completed fetched barrier rounds and immediate reuse. No finiteness of
external scheduling is assumed or promised. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent
open Ptx

def afterRound (s : State n) (generation : Nat) : State n :=
  {lanes := fun t => advance (s.lanes t),barrier := Barrier.reset (generation+1),site := none}

def roundPrefix (s : State n) (pc generation count : Nat) : State n :=
  if count=n then afterRound s generation else
    {s with barrier := Barrier.prefixState generation count,site := if count=0 then none else some pc}

private theorem prefix_dispatch (cfg : Config n) (s : State n) (program : List Instr)
    (pc generation count : Nat) (bound : count<n)
    (pcs : ∀ t, (s.lanes t).pc=pc) (fetch : program[pc]?=some (.sync 0)) :
    ∃ out, Step cfg program ⟨count,bound⟩ (roundPrefix s pc generation count) out ∧
      out.state=roundPrefix s pc generation (count+1) := by
  let t : Fin n := ⟨count,bound⟩
  let c : Barrier.Config n := ⟨cfg.cta,0,pc,cfg.nonempty⟩
  let r : Barrier.Request n := ⟨⟨cfg.cta,0,generation,pc⟩,t⟩
  let start := roundPrefix s pc generation count
  have ne : count≠n := by omega
  have hc : barrierConfig cfg start t=c := by
    simp [barrierConfig,start,roundPrefix,ne,pcs,c]; split <;> rfl
  have hr : barrierRequest cfg start t 0=r := by
    simp [barrierRequest,start,roundPrefix,ne,pcs,r,Barrier.prefixState]
  have hb : start.barrier=Barrier.prefixState generation count := by simp [start,roundPrefix,ne]
  have fresh : Barrier.Runnable (Barrier.prefixState generation count) t := by
    simp [Barrier.Runnable,Barrier.prefixState,t]
  have same : r.key=Barrier.key c (Barrier.prefixState generation count) := rfl
  have marked : Barrier.mark (Barrier.prefixState generation count) r.thread=Barrier.prefixState generation (count+1) :=
    Barrier.mark_prefix generation count bound
  refine ⟨synchronize cfg start t 0,?_,?_⟩
  · refine ⟨?_,.sync 0,?_,Dispatch.sync⟩
    · simpa [start,roundPrefix,ne,Barrier.Runnable,t] using fresh
    · simpa [start,roundPrefix,ne,pcs] using fetch
  · by_cases last : count+1=n
    · have complete : Barrier.Complete (Barrier.mark (Barrier.prefixState generation count) r.thread) := by
        rw [marked,Barrier.complete_prefix_iff c]; omega
      have h := Barrier.completing_step c (Barrier.prefixState generation count) r same fresh complete
      simp only [synchronize,hc,hr,hb,h]
      simp [start,roundPrefix,ne,last,afterRound,Barrier.prefixState]
    · have incomplete : ¬Barrier.Complete (Barrier.mark (Barrier.prefixState generation count) r.thread) := by
        rw [marked,Barrier.complete_prefix_iff c]; omega
      have h := Barrier.waiting_step c (Barrier.prefixState generation count) r same fresh incomplete
      simp only [synchronize,hc,hr,hb,h]
      simp [start,roundPrefix,ne,last,marked,c]

theorem runs_append (first : Runs cfg program s left middle) (second : Runs cfg program middle right final) :
    Runs cfg program s (left++right) final := by
  induction first with
  | nil => exact second
  | cons step _ ih => simpa [List.append_assoc] using Runs.cons step (ih second)

/-- The witness includes every participant, independently of matrix activity. -/
theorem barrier_round_exists (cfg : Config n) (s : State n) (program : List Instr)
    (pc generation : Nat) (pcs : ∀ t, (s.lanes t).pc=pc)
    (reset : s.barrier=Barrier.reset generation) (site : s.site=none)
    (fetch : program[pc]?=some (.sync 0)) :
    ∃ events, Runs cfg program s events (afterRound s generation) := by
  have base : roundPrefix s pc generation 0=s := by
    have ne : 0≠n := by have := cfg.nonempty; omega
    simp [roundPrefix,ne,Barrier.prefix_zero,← reset,← site]
  have witness : ∀ count, count≤n → ∃ events, Runs cfg program s events (roundPrefix s pc generation count) := by
    intro count bound
    induction count with
    | zero => exact ⟨[],by rw [base]; exact Runs.nil⟩
    | succ count ih =>
      obtain ⟨events,run⟩ := ih (by omega)
      obtain ⟨out,step,next⟩ := prefix_dispatch cfg s program pc generation count (by omega) pcs fetch
      have one : Runs cfg program (roundPrefix s pc generation count) out.events (roundPrefix s pc generation (count+1)) := by
        simpa only [List.append_nil,next] using Runs.cons step (Runs.nil (s:=out.state))
      exact ⟨events++out.events,runs_append run one⟩
  simpa [roundPrefix] using witness n (Nat.le_refl n)

theorem two_barriers_exist (cfg : Config n) (s : State n)
    (pcs : ∀ t, (s.lanes t).pc=0) (reset : s.barrier=Barrier.reset 0) (site : s.site=none) :
    ∃ events, Runs cfg [.sync 0,.sync 0] s events (afterRound (afterRound s 0) 1) := by
  obtain ⟨first,hfirst⟩ := barrier_round_exists cfg s [.sync 0,.sync 0] 0 0 pcs reset site rfl
  obtain ⟨second,hsecond⟩ := barrier_round_exists cfg (afterRound s 0) [.sync 0,.sync 0] 1 1
    (by intro t; simp [afterRound,advance,pcs]) rfl rfl rfl
  exact ⟨first++second,runs_append hfirst hsecond⟩

theorem missing_blocks_release (cfg : Config n) (s : State n) (selected other : Fin n)
    (different : other≠selected) (missing : s.barrier.arrived other=false) :
    (Barrier.step (barrierConfig cfg s selected) s.barrier (barrierRequest cfg s selected 0)).disposition ≠ .released :=
  Barrier.missing_other_blocks_release _ _ _ _ different missing

end PtxTorchLean.Poisson.PTX.Concurrent
